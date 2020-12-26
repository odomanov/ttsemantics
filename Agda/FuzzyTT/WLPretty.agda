-- Pretty print module based on Philip Wadler's "prettier printer".
-- Derived from wl-pprint v1.2.1 (https://hackage.haskell.org/package/wl-pprint).
-- Version 0.1.

module WLPretty where

open import Agda.Builtin.Float using (primRound; primFloatTimes; primNatToFloat)
open import Data.Bool 
open import Data.Char renaming (Char to BChar) 
open import Data.Float hiding (⌊_⌋; _+_)
open import Data.Integer using (ℤ; ∣_∣) 
open import Data.List as L hiding (align) 
open import Data.Maybe hiding (align)
open import Data.Nat as ℕ
open import Data.Nat.Show using (show)
open import Data.Product
open import Data.String as S renaming (_++_ to _+++_) hiding (braces; parens; _<+>_; words) 
open import Function using (_∘_; id)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary.Decidable

infixr 5 _</>_ _<//>_ _<$>_ _<$$>_
infixr 6 _<+>_ _<>_

data Doc : Set where
  Empty   : Doc
  Char    : BChar → Doc      -- invariant: char is not '\n'
  Text    : ℕ → String → Doc -- invariant: text doesn't contain '\n'
  Line    : Bool → Doc       -- True <=> when undone by group, do not insert a space
  Cat     : Doc → Doc → Doc
  Nest    : ℕ → Doc → Doc    -- TODO: nest may be negative
  Union   : Doc → Doc → Doc  -- invariant: first lines of first doc longer than
                             -- the first lines of the second doc
  Column  : (ℕ → Doc) → Doc
  Nesting : (ℕ → Doc) → Doc 

-- Normalized Doc for easier printing
data SimpleDoc : Set where
  SEmpty : SimpleDoc
  SChar  : BChar → SimpleDoc → SimpleDoc
  SText  : ℕ → String → SimpleDoc → SimpleDoc
  SLine  : ℕ → SimpleDoc → SimpleDoc


-----------------------------------------------------------
-- Basic Doc constructors
-----------------------------------------------------------

empty : Doc
empty = Empty

line : Doc
line = Line false

linebreak : Doc
linebreak = Line true

char : BChar → Doc
char '\n' = line
char c = Char c

text : String → Doc
text "" = Empty
text s  = Text (S.length s) s

beside : Doc → Doc → Doc
beside x y = Cat x y

nest : ℕ → Doc → Doc
nest i x = Nest i x

column : (ℕ → Doc) → Doc
column f = Column f

nesting : (ℕ → Doc) → Doc
nesting f = Nesting f

spaces : ℕ → String
spaces zero    = ""
spaces (suc n) = " " +++ spaces n

flatten : Doc → Doc
flatten (Cat x y)       = Cat (flatten x) (flatten y)
flatten (Nest i x)      = Nest i (flatten x)
flatten (Line break)    = if break then Empty else Text 1 " "
flatten (Union x y)     = flatten x
flatten (Column f)      = Column (flatten ∘ f)
flatten (Nesting f)     = Nesting (flatten ∘ f)
flatten other           = other                     --Empty,Char,Text

group : Doc → Doc
group x = Union (flatten x) x

_<>_ : Doc → Doc → Doc
x <> y = Cat x y  

-- open Semigroup {{...}}

-- instance
--   sgDoc : Semigroup lzero lzero Doc
--   Carrier {{sgDoc}} = Doc
--   x ≈ y {{sgDoc}} = x ≟ y
--   x ∙ y {{sgDoc}} = x <> y

-- open Monoid {{...}}

-- instance
--   monDoc : Monoid Doc 
--   mempty = empty
--   mappend = _<>_


------------------------------------------------------------------------
-- Utility functions (could be later replaced by standard ones)
------------------------------------------------------------------------

folddoc : (Doc → Doc → Doc) → List Doc → Doc 
folddoc f [] = empty
folddoc f (x ∷ []) = x
folddoc f (x ∷ xs) = f x (folddoc f xs)

private
  -- split a character list at the character ci as a separator
  splitCL : BChar → List BChar → List (List BChar)
  splitCL ci cs with cs
  ... | [] = []
  ... | (c ∷ []) with c Data.Char.== ci
  ...             | true  = []
  ...             | false = (c ∷ []) ∷ []
  splitCL ci cs | (c1 ∷ c2 ∷ css) = step ci c1 c2 (splitCL ci (c2 ∷ css))
    where
    -- add c1 taking into account c2
    step : BChar → BChar → BChar → List (List BChar) → List (List BChar)
    step ci c1 c2 cs with ci Data.Char.== c1 | ci Data.Char.== c2 | cs
    ... | true | _    | _        = cs
    ... | _    | true | _        = (c1 ∷ []) ∷ cs     -- start a new list
    ... | _    | _    | []       = (c1 ∷ []) ∷ [] 
    ... | _    | _    | (x ∷ xs) = (c1 ∷ x) ∷ xs      -- add to the existing list


-- split at space
words : String → List String
words s = L.map fromList (splitCL ' ' (toList s))

-- split at newline
lines : String → List String
lines s = L.map fromList (splitCL '\n' (toList s))


--------------------------------------------
-- More constructors
--------------------------------------------

softline : Doc
softline = group line

softbreak : Doc
softbreak = group linebreak

align : Doc → Doc
align d = column (λ k →
                  nesting (λ i → nest (k ∸ i) d))   --nesting might be negative :-)

hang : ℕ → Doc → Doc
hang i d = align (nest i d)

indent : ℕ → Doc → Doc
indent i d = hang i (text (spaces i) <> d)


-- single characters

lparen : Doc
lparen = char '('

rparen : Doc
rparen = char ')'

langle : Doc
langle = char '<'

rangle : Doc
rangle = char '>'

lbrace : Doc
lbrace = char '{'

rbrace : Doc
rbrace = char '}'

lbracket : Doc
lbracket = char '['

rbracket : Doc
rbracket = char ']'

squote : Doc
squote = char '\''

dquote : Doc
dquote = char '"'

semi : Doc
semi = char ';'

colon : Doc
colon = char ':'

comma : Doc
comma = char ','

space : Doc
space = char ' '

dot : Doc
dot = char '.'

backslash : Doc
backslash = char '\\'

equals : Doc
equals = char '='


-- enclosed docs

enclose : Doc → Doc → Doc → Doc
enclose l r x = l <> x <> r

squotes : Doc → Doc
squotes = enclose squote squote

dquotes : Doc → Doc
dquotes = enclose dquote dquote

braces : Doc → Doc
braces = enclose lbrace rbrace

parens : Doc → Doc
parens = enclose lparen rparen

angles : Doc → Doc
angles = enclose langle rangle

brackets : Doc → Doc
brackets = enclose lbracket rbracket


-- combining Docs

_<+>_ : Doc → Doc → Doc
x <+> y = x <> space <> y

_<$>_ : Doc → Doc → Doc
x <$> y = x <> line <> y

_<$$>_ : Doc → Doc → Doc
x <$$> y = x <> linebreak <> y

_</>_ : Doc → Doc → Doc
x </> y = x <> softline <> y

_<//>_ : Doc → Doc → Doc
x <//> y = x <> softbreak <> y



-- Combinators for basic types

fillwords : String → Doc
fillwords = folddoc _</>_ ∘ L.map text ∘ words

-- replaces spaces and newlines with corresponding Docs
string : String → Doc
string = folddoc _<$$>_ ∘ L.map fillwords ∘ lines

bool : Bool → Doc
bool true  = text ("true")
bool false = text ("false")

nat : ℕ → Doc
nat i = text (Data.Nat.Show.show i)

integer : ℤ → Doc
integer i = text (Data.Integer.show i)

float : Float → Doc
float f = text (Data.Float.show f)



-- List combinators

fillSep : List Doc → Doc
fillSep = folddoc _</>_

hsep : List Doc → Doc
hsep = folddoc _<+>_

vsep : List Doc → Doc
vsep = folddoc _<$>_

sep : List Doc → Doc
sep = group ∘ vsep

fillCat : List Doc → Doc
fillCat = folddoc _<//>_

hcat : List Doc → Doc
hcat = folddoc _<>_

vcat : List Doc → Doc
vcat = folddoc _<$$>_

cat : List Doc → Doc
cat = group ∘ vcat

punctuate : Doc → List Doc → List Doc
punctuate p [] = []
punctuate p (d ∷ []) = (d ∷ [])
punctuate p (d ∷ ds) = (d <> p) ∷ punctuate p ds

-- TODO: add align
encloseSep : Doc → Doc → Doc → List Doc → Doc
encloseSep left right sep [] = left <> right
encloseSep left right sep (x ∷ []) = left <> x <> right 
-- encloseSep left right sep xs = left <> ssep sep xs <> right
encloseSep left right sep xs = left <> folddoc (λ x y → x <> sep <> y) xs <> right
  --align (cat (zipWith _<>_ (left ∷ repeat sep) ds) <> right)
  -- where
  -- fsep : Doc → Doc → Doc 
  -- fsep x y = x <> sep <> y  
  -- ssep : Doc → List Doc → Doc
  -- ssep _   [] = empty
  -- ssep _   (x ∷ []) = x
  -- ssep sep (x ∷ xs) = x <> sep <> ssep xs

list : List Doc → Doc
list = encloseSep lbracket rbracket comma

tupled : List Doc → Doc
tupled = encloseSep lparen rparen comma

semiBraces : List Doc → Doc
semiBraces = encloseSep lbrace rbrace semi


-- alined combinators

-- f = Doс, добавляемый после d; он зависит от длины d
width : Doc → (ℕ → Doc) → Doc
width d f = column (λ k1 → d <> column (λ k2 → f (k2 ∸ k1)))

-- | The document @(fillBreak i x)@ first renders document @x@. It
-- than appends @space@s until the width is equal to @i@. If the
-- width of @x@ is already larger than @i@, the nesting level is
-- increased by @i@ and a @line@ is appended. When we redefine @ptype@
-- in the previous example to use @fillBreak@, we get a useful
-- variation of the previous output:
--
-- > ptype (name,tp)
-- >        = fillBreak 6 (text name) <+> text "::" <+> text tp
--
-- The output will now be:
--
-- @
-- let empty  :: Doc
--     nest   :: Int -> Doc -> Doc
--     linebreak
--            :: Doc
-- @
fillBreak : ℕ → Doc → Doc
fillBreak i x = width x (λ w →
                if ⌊ (w >? i) ⌋ then  nest i linebreak
                             else text (spaces (i ∸ w)))

-- | The document @(fill i x)@ renders document @x@. It than appends
-- @space@s until the width is equal to @i@. If the width of @x@ is
-- already larger, nothing is appended. This combinator is quite
-- useful in practice to output a list of bindings. The following
-- example demonstrates this.
--
-- > types  = [("empty","Doc")
-- >          ,("nest","Int -> Doc -> Doc")
-- >          ,("linebreak","Doc")]
-- >
-- > ptype (name,tp)
-- >        = fill 6 (text name) <+> text "::" <+> text tp
-- >
-- > test   = text "let" <+> align (vcat (map ptype types))
--
-- Which is layed out as:
--
-- @
-- let empty  :: Doc
--     nest   :: Int -> Doc -> Doc
--     linebreak :: Doc
-- @
fill : ℕ → Doc → Doc
fill i d = width d (λ w → if ⌊ (w ℕ.≥? i) ⌋ then empty else text (spaces (i ∸ w)))



-----------------------------------------------------------
-- overloading "pretty", the Pretty class
-----------------------------------------------------------

record Pretty {a} (A : Set a) : Set a where
  field
    pretty        : A → Doc
  prettyList : List A → Doc
  prettyList = list ∘ L.map pretty

open Pretty {{...}} public

instance
  ppList : {A : Set} {p : Pretty A} → Pretty (List A) 
  pretty {{ppList {p = p}}} = Pretty.prettyList p 

  ppDoc : Pretty Doc 
  pretty {{ppDoc}} = id

  ppBool : Pretty Bool 
  pretty {{ppBool}} b = bool b

  ppChar : Pretty BChar 
  pretty {{ppChar}} c = char c

  ppString : Pretty String 
  pretty {{ppString}} s = text s

  ppℕ : Pretty ℕ 
  pretty {{ppℕ}} i = nat i

  ppℤ : Pretty ℤ
  pretty {{ppℤ}} i = integer i

  ppFloat : Pretty Float 
  pretty {{ppFloat}} f = float f

  ppMaybe : {A : Set} {p : Pretty A} → Pretty (Maybe A) 
  pretty {{ppMaybe}} nothing  = empty
  pretty {{ppMaybe {p = p}}} (just x) = (Pretty.pretty p) x

  -- instance (Pretty a,Pretty b) => Pretty (a,b) where
    -- pretty (x,y) = tupled [pretty x, pretty y]
  
  -- instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
    -- pretty (x,y,z)= tupled [pretty x, pretty y, pretty z]
  



-----------------------------------------------------------
-- renderPretty: the default pretty printing algorithm
-----------------------------------------------------------

fits : ℕ → SimpleDoc → Bool
fits _ SEmpty = true
fits w (SChar _ x)   = if ⌊ (w ℕ.<? 1) ⌋ then false else fits (w ∸ 1) x
fits w (SText l _ x) = if ⌊ (w ℕ.<? l) ⌋ then false else fits (w ∸ l) x
fits _ (SLine _ _) = true


{-# TERMINATING #-}
renderPretty : Float → ℕ → Doc → SimpleDoc
renderPretty rfrac w x = best 0 0 ((0 , x) ∷ [])
    where
    -- r : the ribbon width in characters
    -- "The ribbon is the part of a line that is printed, i.e. the line
    -- length without the leading indentation. The layouters take a ribbon
    -- fraction argument, which specifies how much of a line should be
    -- filled before trying to break it up. A ribbon width of 0.5 in a
    -- document of width 80 will result in the layouter to try to not
    -- exceed 0.5*80 = 40 (ignoring current indentation depth)."
    r = 0 ℕ.⊔ (w ℕ.⊓ ∣ primRound (primFloatTimes (primNatToFloat w) rfrac) ∣)

    -- nicest : r = ribbon width, w = page width,
    --          n = indentation of current line, k = current column
    --          x and y, the (simple) documents to chose from.
    --          precondition: first lines of x are longer than the first lines of y.
    nicest : ℕ → ℕ → SimpleDoc → SimpleDoc → SimpleDoc
    nicest n k x y = if fits ((w ∸ k) ℕ.⊓ (r ∸ k + n)) x then x else y

    -- best : n = indentation of current line
    --        k = current column
    --        (ie. (k >= n) && (k - n == count of inserted characters)
    best : ℕ → ℕ → List (ℕ × Doc) → SimpleDoc
    best n k []                     = SEmpty
    best n k ((i , Empty) ∷ ds)     = best n k ds
    best n k ((i , Char c) ∷ ds)    = SChar c (best n (k + 1) ds)
    best n k ((i , Text l s) ∷ ds)  = SText l s (best n (k + l) ds)
    best n k ((i , Line _) ∷ ds)    = SLine i (best i i ds)
    best n k ((i , Cat x y) ∷ ds)   = best n k ((i , x) ∷ (i , y) ∷ ds)
    best n k ((i , Nest j x) ∷ ds)  = best n k ((i + j , x) ∷ ds)
    best n k ((i , Union x y) ∷ ds) = nicest n k (best n k ((i , x) ∷ ds))
                                                 (best n k ((i , y) ∷ ds))
    best n k ((i , Column f) ∷ ds)  = best n k ((i , (f k)) ∷ ds)
    best n k ((i , Nesting f) ∷ ds) = best n k ((i , (f i)) ∷ ds)

-----------------------------------------------------------
-- renderCompact: renders documents without indentation
--  fast and fewer characters output, good for machines
-----------------------------------------------------------

{-# TERMINATING #-}
renderCompact : Doc → SimpleDoc
renderCompact x = scan 0 [ x ]
    where
    scan : ℕ → List Doc → SimpleDoc
    scan k []     = SEmpty
    scan k (Empty ∷ ds)       = scan k ds
    scan k ((Char c) ∷ ds)    = SChar c (scan (k + 1) ds)
    scan k ((Text l s) ∷ ds)  = SText l s (scan (k + l) ds)
    scan k ((Line _) ∷ ds)    = SLine 0 (scan 0 ds)
    scan k ((Cat x y) ∷ ds)   = scan k (x ∷ y ∷ ds)
    scan k ((Nest j x) ∷ ds)  = scan k (x ∷ ds)
    scan k ((Union x y) ∷ ds) = scan k (y ∷ ds)
    scan k ((Column f) ∷ ds)  = scan k (f k ∷ ds)
    scan k ((Nesting f) ∷ ds) = scan k (f 0 ∷ ds)



-----------------------------------------------------------
-- Layout (for SimpleDoc)
-----------------------------------------------------------

layout : SimpleDoc → String
layout SEmpty        = ""
layout (SChar c x)   = fromChar c +++ layout x
layout (SText l s x) = s +++ layout x
layout (SLine i x)   = "\n" +++ spaces i +++ layout x



-- A sort of "standard" pretty printing functions

ppretty : ℕ → Doc → String
ppretty n d = layout (renderPretty 1.0 n d)

-- pprint : ∀ {a} {A : Set a} {p : Pretty A} → ℕ → A → String
-- pprint {p = p} n x = layout (renderPretty 1.0 n (pretty {{p}} x))

--------------------------------------------
-- the PPrint class
--------------------------------------------

record PPrint {a} (A : Set a) : Set a where
  field
    prettytype : Pretty A
  pprint : ℕ → A → String
  pprint n x = layout (renderPretty 1.0 n (pretty {{prettytype}} x))

open PPrint {{...}} public

