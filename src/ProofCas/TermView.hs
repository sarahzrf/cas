{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module ProofCas.TermView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Utils.Pretty
import Utils.ABT
import Utils.Plicity
import Utils.Telescope
import Utils.Vars
import DependentImplicit.Core.Term
import Control.Lens
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Foldable
import Data.Functor.Compose
import Data.List
import Data.Maybe
import qualified Data.Text as T
import ProofCas.Hovering
import ProofCas.Paths (TPath, StPart)
import ProofCas.SetDrag
import ProofCas.WriterInstances

wrapDomEvent' ::
  (IsElement e, PerformEvent t m, TriggerEvent t m) =>
  e -> EventName en -> EventM e (EventType en) b -> m ()
wrapDomEvent' el en a = do
  e <- wrapDomEvent el (onEventName en) a
  performEvent_ (return () <$ e)

ownEvent ::
  (Reflex t, MonadWidget t m,
   IsElement (RawElement d), IsEvent (EventType en)) =>
  EventName en -> Element EventResult d t -> m (Event t Bool)
ownEvent en el = ffilter id <$> eventWithIsOwn en el


data TermEvents t pa =
  TermEvents {
    termClick :: Event t (StPart, pa),
    termDrag  :: Event t (StPart, pa),
    termDrop  :: Event t (StPart, pa)
  }

data RenderCtx t pa =
  RenderCtx {
    selection :: Demux t (Maybe (StPart, pa))
  }

type Render t pa m = WriterT [TermEvents t pa] (ReaderT (RenderCtx t pa) m) ()

termEvents ::
  Reflex t => (StPart, pa)-> Event t a -> Event t b -> Event t c -> TermEvents t pa
termEvents stpa clickE dragE dropE =
  TermEvents (stpa <$ clickE) (stpa <$ dragE) (stpa <$ dropE)

runRender :: Monad m => RenderCtx t pa -> Render t pa m -> m [TermEvents t pa]
runRender ctx = flip runReaderT ctx . execWriterT


termSpan ::
  (Reflex t, MonadWidget t m, Eq pa) => T.Text -> (StPart, pa) -> Render t pa m -> Render t pa m
termSpan termType stpa contents = do
  selection <- asks selection
  rec
    hov <- holdDyn False =<< hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_element_raw span) (onEventName Drop) (False <$ stopPropagation)
    dragHov <- holdDyn False $ leftmost [dropE, dragHovE]
    let selected = demuxed selection (Just stpa)

    let classes = classesFor $
         "term-mouseover" =: hov <>
         "term-dragenter" =: dragHov <>
         "term-selected" =: selected

        plainAttrs = constDyn $ "draggable" =: "true" <> "class" =: termType
        attrs      = addClasses classes plainAttrs

    (span, _) <- elDynAttr' "span" attrs contents

  wrapDomEvent' (_element_raw span) Dragover preventDefault
  dragE <- wrapDomEvent (_element_raw span) (onEventName Dragstart)
    (setCurrentDragData "dummy" "dummy" >> stopPropagation)
  clickedE <- ownEvent Click span
  let eEvs = termEvents stpa clickedE dragE dropE
  tell [eEvs]


textSpan :: MonadWidget t m => T.Text -> m ()
textSpan = elClass "span" "text" . text

sepBy :: MonadWidget t m => T.Text -> [a] -> (a -> m b) -> m [b]
sepBy sep as f = fmap catMaybes . sequence . intersperse sepM . map f' $ as
  where sepM = Nothing <$ textSpan sep
        f'   = fmap Just . f

sepBy_ :: MonadWidget t m => T.Text -> [a] -> (a -> m b) -> m ()
sepBy_ sep as f = void $ sepBy sep as f

bracket :: MonadWidget t m => T.Text -> T.Text -> m a -> m a
bracket o c m = textSpan o *> m <* textSpan c

wrapP :: MonadWidget t m => Bool -> Plicity -> m a -> m a
wrapP True  Expl = bracket "(" ")"
wrapP False Expl = id
wrapP _     Impl = bracket "{" "}"


type Renderable e f pa =
  (Recursive e, Base e ~ Compose ((,) pa) f, Functor f, Ord pa)

renderTerm ::
  (Renderable e f pa, MonadWidget t m) =>
  (f e -> f (e, Bool)) ->
  (f e -> T.Text) ->
  (f (Render t pa m) -> Render t pa m) ->
  StPart -> e -> Render t pa m
renderTerm prec cls step part = go
  where
    go e = termSpan (cls t) (part, pa) $ step subterms
      where Compose (pa, t) = project e
            subterms = prec t <&> \(sub, par) -> wrapP par Expl (go sub)


data Term' a = Var' Variable | In' (TermF (Scope' a)) deriving Functor
data Scope' a =
  Scope' {
    names' :: [String],
    freeNames' :: [FreeVar],
    body' :: a
  } deriving Functor

newtype Subterm = Subterm (TPath, Term)
type instance Base Subterm = Compose ((,) TPath) Term'
instance Recursive Subterm where
  project (Subterm (pa, Var v)) = Compose (pa, Var' v)
  project (Subterm (pa, In t)) = Compose (pa, In' t')
    where rescope s (Scope n f b) = Scope' n f (Subterm (s:pa, b))
          rescopeMotive (CaseMotive (BindingTelescope b r)) =
            CaseMotive (BindingTelescope (zipWith (rescope . MotiveArg) [0..] b) (rescope MotiveRet r))
          -- this is incorrect actually :(
          rescopeClause n (Clause p r) =
            Clause (map (fmap (rescope AssertionPatArg)) p) (rescope (ClauseBody n) r)
          t' = case t of
            Defined v  -> Defined v
            Ann t y    -> Ann (rescope AnnTerm t) (rescope AnnType y)
            Type       -> Type
            Fun p d c  -> Fun p (rescope FunArg d) (rescope FunRet c)
            Lam p b    -> Lam p (rescope LamBody b)
            App p f a  -> App p (rescope AppFun f) (rescope (AppArg p) a)
            Con i a    -> Con i (zipWith (\n (p, a) -> (p, rescope (ConArg p n) a)) [0..] a)
            Case a o c -> Case (zipWith (rescope . CaseArg) [0..] a) (rescopeMotive o) (zipWith rescopeClause [0..] c)

sfpPrec :: Term' Subterm -> Term' (Subterm, Bool)
sfpPrec = fmap go
  where
    go sub@(Subterm (pa, t))
      | s:_ <- pa = (sub, not (parenLoc t s))
      | otherwise = (sub, False)

sfpCls :: Term' a -> T.Text
sfpCls = \case
  Var' (Free _)     -> "free"
  Var' (Bound _ _)  -> "bound"
  Var' (Meta _)     -> "meta"
  In'  (Defined _)  -> "defined"
  In'  (Ann _ _)    -> "ann"
  In'  Type         -> "type"
  In'  (Fun _ _ _)  -> "fun"
  In'  (Lam _ _)    -> "lam"
  In'  (App _ _ _)  -> "app"
  In'  (Con _ _)    -> "con"
  In'  (Case _ _ _) -> "case"

sfpStep :: MonadWidget t m => Term' (Render t pa m) -> Render t pa m
sfpStep (Var' v) = textSpan . T.pack . name $ v
sfpStep (In' t) = case t of
  Defined v  -> textSpan (T.pack v)
  Ann t y    -> body' t >> textSpan " : " >> body' y
  Type       -> textSpan "Type"
  Fun p d c  -> do
    wrapP True p $ do
      textSpan $ T.pack (unwords (names' c)) <> " : "
      body' d
    textSpan " \8594 "
    body' c
  Lam p b    -> do
    textSpan "\955"
    wrapP False p . textSpan . T.pack . unwords . names' $ b
    textSpan " \8594 "
    body' b
  App p f a  -> body' f >> textSpan " " >> wrapP False p (body' a)
  Con i []   -> textSpan (T.pack i)
  Con i a    -> do
    textSpan $ T.pack i <> " "
    sepBy_ " " a $ \(p, a) -> wrapP False p $ body' a
  Case a o c -> do
    textSpan "case "
    sepBy_ " || " a body'

    textSpan " motive "
    let CaseMotive (BindingTelescope b r) = o
    forM_ (zip b (names' r)) $ \(b, v) -> do
      textSpan $ "(" <> T.pack v <> " : "
      body' b
      textSpan ") || "
    body' r

    textSpan " of "
    sepBy_ " | " c $ \(Clause p r) -> do
      textSpan $ T.pack . intercalate " || " . map (const "placeholder" :: PatternF (Scope' (Render t pa m)) -> [Char]) $ p
      textSpan " \8594 "
      body' r

    textSpan " end"

