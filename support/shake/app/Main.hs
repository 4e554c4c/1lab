{-# LANGUAGE BlockArguments, OverloadedStrings, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
module Main (main) where

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Writer

import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import qualified Data.Map.Lazy as Map
import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Digest.Pure.SHA
import Data.Map.Lazy (Map)
import Data.Generics
import Data.Foldable
import Data.Maybe
import Data.Text (Text)
import Data.Char (isDigit)
import Data.List

import Development.Shake.FilePath
import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

import Network.URI.Encode (decodeText)

import qualified System.Directory as Dir

import Text.HTML.TagSoup
import Text.DocTemplates

import Text.Pandoc.Citeproc
import Text.Pandoc.Filter
import Text.Pandoc.Walk
import Text.Pandoc
import Text.Printf
import qualified Citeproc as Cite

import Agda.Interaction.FindFile (SourceFile(..))
import Agda.TypeChecking.Monad.Base
import Agda.Interaction.Options
import Agda.Interaction.Imports
import Agda.Compiler.Backend
import Agda.Utils.FileName

import qualified System.Environment as Env
import HTML.Backend
import HTML.Base
import System.IO (IOMode(..), hPutStrLn, withFile)
import Agda

{-
  Welcome to the Horror That Is 1Lab's Build Script.

  Building 1Lab comprises of (roughly) the following steps:
-}
main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="_build", shakeChange=ChangeDigest} $ do
  fileIdMap <- newCache parseFileIdents
  gitCommit <- newCache gitCommit
  gitAuthors' <- addOracleCache (gitAuthors (gitCommit ()))
  let gitAuthors = gitAuthors' . GitAuthors

  {-
    Write @_build/all-pages.agda@. This imports every module in the source tree
    (causing Agda to compile them) as well as importing all builtin modules
    (which is required for fetching type information).

    Once the file is produced, compile them and write the resulting HTML (for
    @.agda@) and markdown (for @.lagda.md@) files to @_build/html0@.
  -}
  "_build/all-pages.agda" %> \out -> do
    files <- sort <$> getDirectoryFiles "src" ["**/*.agda", "**/*.lagda.md"]
    need (map ("src" </>) files)
    let
      toOut x | takeExtensions x == ".lagda.md"
              = moduleName (dropExtensions x) ++ " -- (text page)"
      toOut x = moduleName (dropExtensions x) ++ " -- (code only)"

    writeFileLines out $ "{-# OPTIONS --cubical #-}"
                       : ["open import " ++ toOut x | x <- files]
                      ++ ["import " ++ x ++ " -- (builtin)" | x <- builtinModules]

    liftIO $ Dir.createDirectoryIfMissing True "_build/html0"
    traced "agda" $
      runAgda defaultOptions{optInputFile = Just "_build/all-pages.agda"} $
      compileAgda out

  {-
    For each 1Lab module, read the emitted file from @_build/html0@. If its
    HTML, we just copy it to @_build/html1@. Otherwise we compile the markdown
    to HTML with some additional post-processing steps (see 'buildMarkdown')

    Finally we emit the HTML using the @support/web/template.html@ template
    and run @agda-fold_equations@ on the output.
  -}
  "_build/html1/*.html" %> \out -> do
    need ["_build/all-pages.agda"]

    let
      modname = dropExtension (takeFileName out)
      input = "_build/html0" </> modname

    ismd <- liftIO $ Dir.doesFileExist (input <.> ".md")

    gitCommit <- gitCommit ()

    if ismd
      then buildMarkdown gitCommit gitAuthors (input <.> ".md") out
      else liftIO $ Dir.copyFile (input <.> ".html") out

  {-
    @_build/html1@ now contains all processed 1Lab modules in HTML form. We now
    'just' need to do some additional post-processing before copying them into
    our final @_build/html@ output folder.

     - Replace @agda://xyz@ links with a link to the actual definition
       ('parseAgdaLink').
     - Check the markup for raw <!-- or -->, which indicates a misplaced
       comment ('checkMarkup').
  -}
  "_build/html/*.html" %> \out -> do
    let input = "_build/html1" </> takeFileName out
    need [input]

    text <- liftIO $ Text.readFile input
    tags <- traverse (parseAgdaLink fileIdMap) (parseTags text)
    traverse_ (checkMarkup (takeFileName out)) tags
    liftIO $ Text.writeFile out (renderHTML5 tags)

  "_build/html/static/links.json" %> \out -> do
    need ["_build/html1/all-pages.html"]
    (start, act) <- runWriterT $ findLinks (tell . Set.singleton) . parseTags
      =<< liftIO (readFile "_build/html1/all-pages.html")
    need (Set.toList act)
    traced "crawling links" . withFile out WriteMode $ \h -> do
      hPutStrLn h "["
      crawlLinks
        (\x o -> liftIO $ hPrintf h "[%s, %s],"
          (show (dropExtension x))
          (show (dropExtension o)))
        (const (pure ()))
        (Set.toList start)
      hPutStrLn h "null]"

  "_build/html/static/search.json" %> \out -> do
    need ["_build/html1/all-pages.html"]
    copyFile' "_build/all-types.json" out

  -- Compile Quiver to SVG. This is used by 'buildMarkdown'.
  "_build/html/*.svg" %> \out -> do
    let inp = "_build/diagrams" </> takeFileName out -<.> "tex"
    need [inp]
    command_ [Traced "build-diagram"] "sh"
      ["support/build-diagram.sh", out, inp]
    removeFilesAfter "." ["rubtmp*"]

  latexRules

  "_build/html/css/*.css" %> \out -> do
    let inp = "support/web/css/" </> takeFileName out -<.> "scss"
    getDirectoryFiles "support/web/css" ["**/*.scss"] >>= \files -> need ["support/web/css" </> f | f <- files]
    command_ [] "sassc" [inp, out]

  "_build/html/favicon.ico" %> \out -> do
    need ["support/favicon.ico"]
    copyFile' "support/favicon.ico" out

  "_build/html/static/**/*" %> \out -> do
    let inp = "support/" </> dropDirectory1 (dropDirectory1 out)
    need [inp]
    traced "copying" $ Dir.copyFile inp out

  "_build/html/*.js" %> \out -> do
    getDirectoryFiles "support/web/js" ["**/*.ts", "**/*.tsx"] >>= \files -> need ["support/web/js" </> f | f <- files]

    let inp = "support/web/js" </> takeFileName out -<.> "ts"
    command_ [] "node_modules/.bin/esbuild"
      [ "--bundle", inp
      , "--outfile=" ++ out
      , "--target=es2017"
      , "--minify"
      , "--sourcemap"
      ]

  {-
    The final build step. This basically just finds all the files we actually
    need and kicks off the above job to build them.
  -}
  phony "all" do
    need ["_build/all-pages.agda"]
    files <- filter ("open import" `isPrefixOf`) . lines <$> readFile' "_build/all-pages.agda"
    need $ "_build/html/all-pages.html"
         : [ "_build/html" </> (words file !! 2) <.> "html"
           | file <- files
           ]

    static <- getDirectoryFiles "support/static/" ["**/*"] >>= \files ->
      pure ["_build/html/static" </> f | f <- files]
    agda <- getDirectoryFiles "_build/html0" ["Agda.*.html"] >>= \files ->
      pure ["_build/html/" </> f | f <- files]
    need $ [ "_build/html/favicon.ico"
           , "_build/html/static/links.json"
           , "_build/html/static/search.json"
           , "_build/html/css/default.css"
           , "_build/html/main.js"
           , "_build/html/code-only.js"
           ] ++ static ++ agda

  -- ???

  phony "clean" do
    removeFilesAfter "_build" ["html0/*", "html/*", "diagrams/*", "*.agda", "*.md", "*.html"]

  phony "really-clean" do
    need ["clean"]
    removeFilesAfter "_build" ["**/*.agdai", "*.lua"]

  phony "typecheck-ts" do
    getDirectoryFiles "support/web/js" ["**/*.ts", "**/*.tsx"] >>= \files -> need ["support/web/js" </> f | f <- files]
    command_ [] "node_modules/.bin/tsc" ["--noEmit", "-p", "tsconfig.json"]

  -- Profit!

-- | Write a HTML file, correctly handling the closing of some tags.
renderHTML5 :: [Tag Text] -> Text
renderHTML5 = renderTagsOptions renderOptions{ optMinimize = min } where
  min = flip elem ["br", "meta", "link", "img", "hr"]

--------------------------------------------------------------------------------
-- Various oracles
--------------------------------------------------------------------------------

-- | A link to an identifier in an emitted Agda file of the form @1Lab.Module#1234@.
newtype Reference = Reference Text deriving (Eq, Show)

-- | Parse an Agda module in @_build/html1@ and build a map of all its definitions
-- to their link.
parseFileIdents :: Text -> Action (Map Text Reference, Map Text Text)
parseFileIdents mod =
  do
    let path = "_build/html1" </> Text.unpack mod <.> "html"
    need [ path ]
    traced ("parsing " ++ Text.unpack mod) do
      go mempty mempty . parseTags <$> Text.readFile path
  where
    go fwd rev (TagOpen "a" attrs:TagText name:TagClose "a":xs)
      | Just id <- lookup "id" attrs, Just href <- lookup "href" attrs
      , mod `Text.isPrefixOf` href, id `Text.isSuffixOf` href
      = go (Map.insert name (Reference href) fwd)
           (Map.insert href name rev) xs
      | Just classes <- lookup "class" attrs, Just href <- lookup "href" attrs
      , "Module" `elem` Text.words classes, mod `Text.isPrefixOf` href
      = go (Map.insert name (Reference href) fwd)
           (Map.insert href name rev) xs
    go fwd rev (_:xs) = go fwd rev xs
    go fwd rev [] = (fwd, rev)


-- | Get the current git commit.
gitCommit :: () -> Action String
gitCommit () = do
  Stdout t <- command [] "git" ["rev-parse", "--verify", "HEAD"]
  pure (head (lines t))

newtype GitAuthors = GitAuthors FilePath
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult GitAuthors = [Text]

-- | Get the authors for a particular commit.
gitAuthors :: Action String -> GitAuthors -> Action [Text]
gitAuthors commit (GitAuthors path) = do
  _commit <- commit -- We depend on the commit, but don't actually need it.

  -- Sort authors list and make it unique.
  Stdout authors <- command [] "git" ["log", "--format=%aN", "--", path]
  let authorSet = Set.fromList . Text.lines . Text.decodeUtf8 $ authors

  Stdout coauthors <-
    command [] "git" ["log", "--format=%(trailers:key=Co-authored-by,valueonly)", "--", path]

  let
    coauthorSet = Set.fromList
      . map dropEmail
      . filter (not . Text.null . Text.strip)
      . Text.lines
      . Text.decodeUtf8 $ coauthors

    dropEmail = Text.unwords . init . Text.words

  pure . Set.toList $ authorSet <> coauthorSet

--------------------------------------------------------------------------------
-- Markdown Compilation
--------------------------------------------------------------------------------

data MarkdownState = MarkdownState
  { mdReferences :: [Val Text]
  , mdDependencies :: [String]
  }

instance Semigroup MarkdownState where
  (MarkdownState r s) <> (MarkdownState r' s') = MarkdownState (r <> r') (s <> s')

instance Monoid MarkdownState where
  mempty = MarkdownState mempty mempty


{-| Convert a markdown file to templated HTML.

After parsing the markdown, we perform the following post-processing steps:
  - Run @agda-reference-filter@ on the parsed Markdown.
  - Put inline equations (@$...$@) in a special @<span>@ to avoid word wrapping.
  - Add header links to each header.
  - For each quiver diagram, write its contents to @_build/diagrams/DIGEST.tex@
    and depend on @_build/html/DIGEST.svg@. This kicks off another build step
    which runs @support/build-diagram.sh@ to build the SVG.
  - For each equation, invoke katex to compile them to HTML. This is cached
    between runs (search for 'LatexEquation' in 'main').
  - Extract the references block (if present), passing it through to the
    template instead. Also add the paper's title to all reference links.
  - Fetch all git authors for this file and add it to the template info.

Finally, we emit the markdown to HTML using the @support/web/template.html@
template, pipe the output of that through @agda-fold-equations@, and write
the file.
-}
buildMarkdown :: String
              -> (FilePath -> Action [Text])
              -> FilePath -> FilePath -> Action ()
buildMarkdown gitCommit gitAuthors input output = do
  let
    templateName = "support/web/template.html"
    bibliographyName = "src/bibliography.bibtex"
    modname = dropDirectory1 (dropDirectory1 (dropExtension input))

  need [templateName, bibliographyName, input]

  modulePath <- findModule modname
  authors <- gitAuthors modulePath
  let
    permalink = gitCommit </> modulePath

    title
      | length modname > 24 = '…':reverse (take 24 (reverse modname))
      | otherwise = modname

    mStr = MetaString . Text.pack
    patchMeta
      = Meta
      . Map.insert "title" (mStr title)
      . Map.insert "source" (mStr permalink)
      . Map.insert "bibliography" (mStr bibliographyName)
      . Map.insert "link-citations" (MetaBool True)
      . unMeta

  (markdown, references) <- liftIO do
    contents <- Text.readFile input
    either (fail . show) pure =<< runIO do
      markdown <- readMarkdown def { readerExtensions = getDefaultExtensions "markdown" } [(input, contents)]
      Pandoc meta markdown <- applyFilters def [JSONFilter "agda-reference-filter"] ["html"] markdown
      let pandoc = Pandoc (patchMeta meta) markdown
      (,) <$> processCitations pandoc <*> getReferences Nothing pandoc

  let
    htmlInl = RawInline (Format "html")

    refMap = Map.fromList $ map (\x -> (Cite.unItemId . Cite.referenceId $ x, x)) references

    -- | Replace any expression $foo$-bar with <span ...>$foo$-bar</span>, so that
    -- the equation is not split when word wrapping.
    patchInlines (m@Math{}:s@(Str txt):xs)
      | not (Text.isPrefixOf " " txt)
      = htmlInl "<span style=\"white-space: nowrap;\">" : m : s : htmlInl "</span>"
      : patchInlines xs
    patchInlines (x:xs) = x:patchInlines xs
    patchInlines [] = []

    -- Make all headers links, and add an anchor emoji.
    patchBlock (Header i a@(ident, _, _) inl) = pure $ Header i a
      $ htmlInl (Text.concat ["<a href=\"#", ident, "\" class=\"header-link\">"])
      : inl
      ++ [htmlInl "<span class=\"header-link-emoji\">🔗</span></a>"]
    -- Replace quiver code blocks with a link to an SVG file, and depend on the SVG file.
    patchBlock (CodeBlock (id, classes, attrs) contents) | "quiver" `elem` classes = do
      let
        digest = showDigest . sha1 . LazyBS.fromStrict $ Text.encodeUtf8 contents
        title = fromMaybe "commutative diagram" (lookup "title" attrs)
      liftIO $ Text.writeFile ("_build/diagrams" </> digest <.> "tex") contents
      tell mempty { mdDependencies = ["_build/html" </> digest <.> "svg"] }

      pure $ Div ("", ["diagram-container"], [])
        [ Plain [ Image (id, "diagram":classes, attrs) [] (Text.pack (digest <.> "svg"), title) ]
        ]
    -- Find the references block, parse the references, and remove it. We write
    -- the references as part of our template instead.
    patchBlock (Div ("refs", _, _) body) = do
      for_ body \ref -> case ref of
        (Div (id, _, _) body) -> do
          -- If our citation is a single paragraph, don't wrap it in <p>.
          let body' = case body of
                [Para p] -> [Plain p]
                body -> body
          -- Now render it the citation itself to HTML and add it to our template
          -- context.
          body <- either (fail . show) pure . runPure $
            writeHtml5String def { writerExtensions = getDefaultExtensions "html" } (Pandoc mempty body')
          let ref = Context $ Map.fromList
                    [ ("id", toVal id)
                    , ("body", toVal body)
                    ]
          tell mempty { mdReferences = [ MapVal ref ]}

        _ -> fail ("Unknown reference node " ++ show ref)
      pure Null

    patchBlock h = pure h

    -- Pre-render latex equations.
    patchInline (Math DisplayMath contents) = htmlInl <$> askOracle (LatexEquation (True, contents))
    patchInline (Math InlineMath contents) = htmlInl <$> askOracle (LatexEquation (False, contents))
    -- Add the title to reference links.
    patchInline (Link attrs contents (target, ""))
      | Just citation <- Text.stripPrefix "#ref-" target
      , Just ref <- Map.lookup citation refMap
      , Just title <- Cite.valToText =<< Cite.lookupVariable "title" ref
      = pure $ Link attrs contents (target, title)
    patchInline h = pure h

  liftIO $ Dir.createDirectoryIfMissing False "_build/diagrams"

  markdown <- pure $ walk patchInlines markdown
  markdown <- walkM patchInline markdown
  (markdown, MarkdownState references dependencies) <- runWriterT (walkM patchBlock markdown)
  need dependencies

  text <- liftIO $ either (fail . show) pure =<< runIO do
    template <- getTemplate templateName >>= runWithPartials . compileTemplate templateName
                >>= either (throwError . PandocTemplateError . Text.pack) pure

    let
      authors' = case authors of
        [] -> "Nobody"
        [x] -> x
        _ -> Text.intercalate ", " (init authors) `Text.append` " and " `Text.append` last authors

      context = Context $ Map.fromList
                [ (Text.pack "is-index", toVal (modname == "index"))
                , (Text.pack "authors", toVal authors')
                , (Text.pack "reference", toVal references)
                ]
      options = def { writerTemplate = Just template
                    , writerTableOfContents = True
                    , writerVariables = context
                    , writerExtensions = getDefaultExtensions "html" }
    writeHtml5String options markdown

  liftIO $ Text.writeFile output text

  -- command_ [] "agda-fold-equations" [output]

-- | Find the original Agda file from a 1Lab module name.
findModule :: MonadIO m => String -> m FilePath
findModule modname = do
  let toPath '.' = '/'
      toPath c = c
  let modfile = "src" </> map toPath modname

  exists <- liftIO $ Dir.doesFileExist (modfile <.> "lagda.md")
  pure $ if exists
    then modfile <.> "lagda.md"
    else modfile <.> "agda"

newtype LatexEquation = LatexEquation (Bool, Text) -- TODO: Less lazy instance
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult LatexEquation = Text

-- | Compile a latex equation to a HTML string.
latexRules :: Rules ()
latexRules = versioned 1 do
  _ <- addOracleCache \(LatexEquation (display, tex)) -> do
    need [".macros"]

    let args = ["-f", ".macros", "-t"] ++ ["-d" | display]
        stdin = LazyBS.fromStrict $ Text.encodeUtf8 tex
    Stdout out <- command [StdinBS stdin] "katex" args
    pure . Text.stripEnd . Text.decodeUtf8 $ out

  pure ()

--------------------------------------------------------------------------------
-- Additional HTML post-processing
--------------------------------------------------------------------------------

-- | Possibly interpret an <a href="agda://"> link to be a honest-to-god
-- link to the definition.
parseAgdaLink :: (Text -> Action (Map Text Reference, Map Text Text))
              -> Tag Text -> Action (Tag Text)
parseAgdaLink fileIds (TagOpen "a" attrs)
  | Just href <- lookup "href" attrs, Text.pack "agda://" `Text.isPrefixOf` href = do
    href <- pure $ Text.splitOn "#" (Text.drop (Text.length "agda://") href)
    let
      cont mod ident = do
        (idMap, _) <- fileIds mod
        case Map.lookup ident idMap of
          Just (Reference href) -> do
            pure (TagOpen "a" (emplace [("href", href)] attrs))
          _ -> error $ "Could not compile Agda link: " ++ show href
    case href of
      [mod] -> cont mod mod
      [mod, ident] -> cont mod (decodeText ident)
      _ -> error $ "Could not parse Agda link: " ++ show href
parseAgdaLink _ x = pure x

emplace :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
emplace ((p, x):xs) ys = (p, x):emplace xs (filter ((/= p) . fst) ys)
emplace [] ys = ys

-- | Check HTML markup is well-formed.
checkMarkup :: FilePath -> Tag Text -> Action ()
checkMarkup file (TagText txt)
  |  "<!--" `Text.isInfixOf` txt || "<!–" `Text.isInfixOf` txt
  || "-->" `Text.isInfixOf` txt  || "–>" `Text.isInfixOf` txt
  = fail $ "[WARN] " ++ file ++ " contains misplaced <!-- or -->"
checkMarkup _ _ = pure ()

--------------------------------------------------------------------------------
-- Loading types from .agdai files
--------------------------------------------------------------------------------

compileAgda :: FilePath -> String -> TCMT IO ()
compileAgda path _ = do
  skipTypes <- liftIO . fmap isJust . Env.lookupEnv $ "SKIP_TYPES"
  source <- parseSource . SourceFile =<< liftIO (absolute path)
  basepn <- liftIO $ absolute "src/"
  cr <- typeCheckMain TypeCheck source
  modifyTCLens stBackends
    (htmlBackend (filePath basepn) defaultHtmlOptions{htmlOptGenTypes = not skipTypes}:)
  callBackend "HTML" IsMain cr

--------------------------------------------------------------------------------
-- Generate all edges between pages
--------------------------------------------------------------------------------

findLinks :: MonadIO m => (String -> m ()) -> [Tag String] -> m (Set.Set String)
findLinks cb (TagOpen "a" attrs:xs)
  | Just href' <- lookup "href" attrs
  , (_, anchor) <- span (/= '#') href'
  , all (not . isDigit) anchor
  = do
    let href = takeWhile (/= '#') href'
    t <- liftIO $ Dir.doesFileExist ("_build/html1" </> href)
    cb ("_build/html1" </> href)
    if (t && Set.notMember href ignoreLinks)
      then Set.insert href <$> findLinks cb xs
      else findLinks cb xs
findLinks k (_:xs) = findLinks k xs
findLinks _ [] = pure mempty

ignoreLinks :: Set.Set String
ignoreLinks = Set.fromList [ "all-pages.html", "index.html" ]

crawlLinks
  :: MonadIO m'
  => (forall m. MonadIO m => String -> String -> m ())
  -> (String -> m' ())
  -> [String]
  -> m' ()
crawlLinks link need = go mempty where
  go _visitd [] = pure ()
  go visited (x:xs)
    | x `Set.member` visited = go visited xs
    | otherwise = do
      links <- findLinks need =<< fmap parseTags (liftIO (readFile ("_build/html1" </> x)))
      for_ links $ \other -> link x other
      go (Set.insert x visited) (Set.toList links ++ xs)