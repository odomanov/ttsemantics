% -*- mode: LaTeX; coding: utf-8 -*-
\documentclass[presentation,smaller]{mybeamer}

% \usepackage{prftree}

\author{О.\,Доманов}
\date{Новосибирск, 21 марта 2019 г.}
\title{Монады и зависимость от контекста в семантике}
% \subtitle{(with solutions to puzzles)}

% \setcounter{tocdepth}{7}

\usepackage{agda}
\newcommand{\agdafont}{\setsansfont{DejaVu Sans Mono}}
\renewcommand{\AgdaCodeStyle}{\small\agdafont}
\setbeamersize{text margin left=3mm,text margin right=3mm}

\usepackage{tcolorbox}
\newtcolorbox{agdacomm}{colback=black!10!white,boxrule=0pt,top=0pt,bottom=0pt}

\begin{document}
\def\mymathskip{.2em}
\abovedisplayshortskip=\mymathskip
\belowdisplayshortskip=\mymathskip
\abovedisplayskip=\mymathskip
\belowdisplayskip=\mymathskip
% \prfinterspace=2em

\maketitle

% \begin{frame}
%   \frametitle{Оглавление}
%   \tableofcontents
% \end{frame}

\section{Теория}

\begin{frame}
  \frametitle{Категория}
  \begin{itemize}
  \item Набор объектов $A, B, \ldots$;
  \item Для каждых двух объектов $A,B$ существует набор морфизмов
    между ними $Hom(A,B)$.
    Обозначение: $f:A → B, \ldots$ или $A\overset{f}→B$.
  \item Для каждых двух морфизмов $f:A → B$,
    $g:B→ C$ существует композиция $g ∘ f:A→ C$;
  \item Композиция ассоциативна: $(f ∘ g) ∘ h = f ∘ (g ∘ h)$;
  \item Для каждого объекта существует единичный морфизм $id_{A}: A → A$,
    такой, что $f∘ id_{A}=f=id_{A}∘ f$;
  \end{itemize}
  \pause
  \begin{itemize}
  \item Функтор $F:\mathcal{C}→\mathcal{D}$
    отображает объекты и морфизмы категории $\mathcal{C}$
    в объекты и морфизмы категории $\mathcal{D}$ с «сохранением
    структуры»:
    \begin{itemize}
    \item $F(id_{A})=id_{F(A)}$
    \item $F(f∘ g)=F(f)∘ F(g)$.
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Теория  категорий и теория типов}
  Существует соответствие между теорией типов и теорией категорий:

  \begin{center}
    \begin{tabular}{l@{$\quad⇔\quad$}l}
      Объекты & Типы (множества) \\
      Морфизмы & Функции 
    \end{tabular}
  \end{center}
  
  Таким образом, $Hom(A,B)$ соответствует типу функций $A→ B$.

  \pause
  Соответствие \alert{не} взаимно однозначное: для каждой теории типов
  имеется категория, но не наоборот.

  Для нас это не имеет значения, поскольку у нас основная семантика
  будет теоретико"=типовой. 
\end{frame}

\begin{frame}
  \frametitle{Теоретико"=типовая семантика}
  % Может быть описана в терминах типов или категорий.

  \begin{tabular*}{\textwidth}%
      {@{}p{.47\textwidth}@{\makebox[.06\textwidth]{$⇒$}}p{.47\textwidth}@{}}
      Нарицательные существительные & Типы/объекты/множества               \\
      Термы                         & Функции $t: A → B$                   \\
      Пропозиции                    & Типы/объекты/множества доказательств \\
      Предикаты (проп. функции)     & Функции $A → Set$                    \\
      Глаголы                       & Функции $A → Set$                    \\
      \textellipsis                 & \textellipsis
  \end{tabular*}

  \pause
  В случае интенсиональной семантики типы $A$
  превращаются в типы $W → A$.\\
  Например, вместо $\text{Столица}: \text{Cтрана} → \text{Город}$
  мы имеем функции
  $\text{Столица}: \text{Страна} → (W → \text{Город}$).

  \pause
  Мы хотим перенести (расширить) операции с экстенсионалами на
  операции с интенсионалами.

  \pause%
  \textbf{Задача в общем виде:} мы имели типы $A, B,\ldots$
  с операциями на них, теперь мы имеем новые типы $MA, MB, \ldots$
  и хотим перенести наши операции на них.
\end{frame}

\begin{frame}
  \frametitle{Понятие вычисления}
  \begin{itemize}
  \item E. Moggi (1991) "--- монада как «понятие вычисления».
  \item $MA$ "--- вычисление со значениями в $A$, но с возможной
    дополнительной структурой.
  \item Помимо $MA = W → A$:
    \begin{itemize}
    \item $MA = \mathcal{P}A$ "--- индетерминизм;
    \item $MA = A × S$, где $S$ "--- множество состояний;
    \item $MA = A + \text{Nothing}$
      "--- результат, возможно, не определён.
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Категория Кляйсли (Kleisli)}
  Задача: расширить операции с $A$ на операции с $MA$.
  \begin{itemize}
  \item Те же объекты, но морфизмами считаем не $f:A→ B$,
    а $\hat{f}:A→ MB$. 
  \item Нужно определить тождественную функцию и композицию функций
    для вычислений $\hat{f}:A → MB$.
  \item Тождественная функция $\eta_{A}: A → MA$.
  \item Вместо
    $A\overset{f}{\longrightarrow}B\overset{g}{\longrightarrow}C$\\
    нужно\\
    $A\overset{\hat{f}}{\longrightarrow} MB \overset{\hat{g}}\longrightarrow MMC
    \overset{?}{\longrightarrow}MC$.
  \item Необходима функция $μ_{A}:MMA → MA$.
  \end{itemize}
  \pause
  Если $\eta, \mu$ (с нужными свойствами) существуют, то
  \begin{enumerate}
  \item функции Кляйсли $A → MB$ составляют категорию;
  \item мы имеем монаду.
  \end{enumerate}
\end{frame}

\begin{frame}
  \frametitle{Функция связывания}
  Применение функции Кляйсли $f:A → MB$ к $a:A$ описывается функцией
  \[
    app: A → (A → MB) → MB.
  \]
  Мы будем использовать более удобную для нас функцию (bind)
  \[
    ⋆: MA → (A → MB) → MB.
  \]
  \pause
  Они связаны следующим образом:
  \[
    % μ_{B}(⋆(\eta_{A}(a),f))=app(a,f),
    ⋆(m, f) = μ(app(m,Mf))
  \]
  \[
    ⋆: MA \xrightarrow{app} MMB \overset{μ}{\longrightarrow} MB.
  \]
  \pause
  Кроме того, будем писать \alert{$m⋆ f$}, тогда можно строить цепочки
  \[
    m⋆ f⋆ g⋆ \ldots
  \]
  где $m:MA$, $f:A → MB$, $g:B → MC$, \textellipsis
\end{frame}

\begin{frame}
  \frametitle{Монада}
  \begin{itemize}
  \item Эндофунктор в категории $\mathcal{C}$,
    то есть $M:\mathcal{C}→ \mathcal{C}$.
  \item Для любого $A\in \mathcal{C}$ существует $\eta: A → MA$.
  \item Для любых $A, B\in \mathcal{C}$
    существует $⋆: MA → (A → MB) → MB$.
  \item $m ⋆ \eta = m$
  \item $\eta\ a ⋆ f = f a$
  \item $(m ⋆ f) ⋆ g = m ⋆ (λx.f x ⋆ g)$
  \end{itemize}

  \pause
  Reader или Function monad:
  \begin{itemize}
  \item $MA = W → A$ \hfill "--- интенсионал
  \item $\eta\ a = λw.a$ \hfill "--- rigid designator
  \item $m ⋆ f = λw.f(m(w))\ w$
  \end{itemize}
\end{frame}

\section{Формализация в Agda}

  \begin{code}[hide]
module Doklad-21-03-2019 where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Monad.Identity
open import Monad.Reader   
  \end{code}

\begin{frame}
  \frametitle{Синтаксис Agda}
  \begin{code}[hide]
postulate
  \end{code}
  \begin{code}[inline]
    B : Set
  \end{code}
,\
  \begin{code}[inline]
    A : B
  \end{code}
\ означает принадлежность типу.
  \begin{code}[hide]
module AgdaSyntax where
  \end{code}

\pause
Определение типа:
  \begin{code}
  data C : Set where
    a b c : C
  \end{code}
\pause
Тип может быть зависимым:
  \begin{code}
  data E : C → Set where
  \end{code}

\makebox[.3\textwidth][l]{Тип $\tprod(x:C)\,Ex\quad⇒$} 
  \begin{code}[hide]
  postulate
  \end{code}
  \begin{code}[inline]
    g : ∀ (x : C) → E x
  \end{code}

\makebox[.3\textwidth][l]{Тип $\tsum(x:C)\,Ex\quad⇒$}  
  \begin{code}[inline]
    h : Σ[ x ∈ C ] E x
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{Синтаксис Agda (2)}
Определение функции:
  \begin{code}[hide]
  data D : Set where
    d e : D
  \end{code}
  \begin{code}
  f : C → D
  f a = d 
  f b = e 
  f c = d 
  \end{code}
\pause
Аналогично записываются теоремы:
  \begin{code}[hide]
  data Пропозиция : Set where
    d : Пропозиция
  \end{code}
  \begin{code}
  prf : Пропозиция
  prf = d 
  \end{code}
\pause
Или даже так:
  \begin{code}
  _ : Пропозиция
  _ = d 
  \end{code}
\pause
Функции можно определять так:
  \begin{code}[hide]
  postulate
  \end{code}
  \begin{code}
    _прибавить_ : C → D → D
  \end{code}
Тогда вместо «{\agdafont прибавить a b}» можно писать «{\agdafont a прибавить b}».
\end{frame}

\begin{frame}
  %\vspace{.5ex}
  \begin{code}[hide]
module ВозможныеМиры where
  \end{code}
  \begin{code}
  data Мир : Set
    where w₁ w₂ : Мир
  IntMonad = MonadReader Мир
  \end{code}
  \begin{agdacomm}Обычное обозначение для интенсионала: $^{∧}A$
  (фактически, {\agdafont ∧} = M).\end{agdacomm}
  \begin{code}
  ∧ : ∀ {i} → Set i → Set i
  ∧ = Reader Мир 
  \end{code}
  \vspace{-2.5ex}
  \begin{code}
  mkIntensional : ∀ {a} {A : Set a} → (Мир → A) → ∧ A
  mkIntensional f = mkReaderT (λ w → mkIdentity (f w))
  \end{code}
  \begin{agdacomm}
    Экстенсионал:
  \end{agdacomm}
  \begin{code}
  ∨ : ∀ {i} {A : Set i} → ∧ A → (Мир → A)
  ∨ = runReader                 
  \end{code}
  \begin{agdacomm}
    {\agdafont ⟦ m ⟧/ w} "--- значение выражения (интенсионала) $m$ в мире $w$
  \end{agdacomm}
  \begin{code}
  ⟦_⟧/_ : ∀ {i} {A : Set i} → ∧ A → Мир → A
  ⟦ ma ⟧/ w = ∨ ma w
  \end{code}
  \begin{code}[hide]
  infixl 5 _★_
  _★_ = _>>=_
  \end{code}
  \begin{agdacomm}
    {\agdafont rigid} "--- функция $\eta$ (rigid designator): 
  \end{agdacomm}
  \begin{code}
  rigid = return
  \end{code}
\end{frame}

\begin{frame}
  \vspace{2ex}
  \begin{code}
  data Человек : Set where
    John Mary Bill Unknown : Человек
  \end{code}
  \begin{agdacomm}
    Пример: rigid designator John
  \end{agdacomm}
  \begin{code}
  iJohn : ∧ Человек
  iJohn = rigid John
  
  _ : ⟦ iJohn ⟧/ w₁ ≡ John
  _ = refl
  
  _ : ⟦ iJohn ⟧/ w₂ ≡ John
  _ = refl
  
  _ : ∀ (w : Мир) → ⟦ iJohn ⟧/ w ≡ John
  _ = λ w → refl
  \end{code}
\end{frame}

\begin{frame}
  \vspace{2ex}
  \begin{agdacomm}
    Более сложный пример.
  \end{agdacomm}
  \begin{code}
  Чемпион : ∧ Человек
  Чемпион = mkIntensional f
    where
    f : Мир → Человек
    f w₁ = John
    f w₂ = Mary
  
  _ : ⟦ Чемпион ⟧/ w₁ ≡ John
  _ = refl
  
  _ : ⟦ Чемпион ⟧/ w₂ ≡ Mary
  _ = refl
  \end{code}
\end{frame}

\begin{frame}%[squeeze]%[shrink=3]
  % \vspace{1ex}
  \begin{agdacomm}
    Рассмотрим пример с зависимыми типами.
  \end{agdacomm}
  \begin{code}
  postulate
    _бежит-в-мире_ : Человек → Мир → Set
    Jr1  : John бежит-в-мире w₁
    Mr2  : Mary бежит-в-мире w₂
    Jr2⊥ : John бежит-в-мире w₂ → ⊥
    Br1  : Bill бежит-в-мире w₁
  \end{code}
  \vspace{-2.5ex}
  \begin{code}
  iБежит : Человек → (∧ Set)
  iБежит h = mkIntensional (λ w → h бежит-в-мире w) 
  
  _ : ⟦ Чемпион ★ iБежит ⟧/ w₁ ≡ John бежит-в-мире w₁
  _ = refl
  \end{code}
  \vspace{-2.5ex}
  \begin{code}
  _ : ⟦ Чемпион ★ iБежит ⟧/ w₁ 
  _ = Jr1
  \end{code}
  \vspace{-2.5ex}
  \begin{code}
  _ : ⟦ Чемпион ★ iБежит ⟧/ w₂ 
  _ = Mr2
  \end{code}
  \vspace{-2.5ex}
  \begin{code}
  _ : ⟦ rigid John ★ iБежит ⟧/ w₂ → ⊥ 
  _ = Jr2⊥ 
  \end{code}
\end{frame}


\begin{frame}
  \vspace{2ex}
  \begin{agdacomm}
    То же для двуместного предиката.
  \end{agdacomm}
  \begin{code}
  postulate
    _любит_в-мире_ : Человек → Человек → Мир → Set
    MlB2   : Mary любит Bill в-мире w₂                  
    lself1 : ∀ (h : Человек) → h любит h в-мире w₁    
    lself2 : ∀ (h : Человек) → h любит h в-мире w₂ → ⊥
    
  iЛюбит : Человек → ∧ (Человек → Set)
  iЛюбит h =
    mkIntensional (λ w → (λ h2 → h любит h2 в-мире w))
  
  _ : ⟦ Чемпион ★ iЛюбит ⟧/ w₁ ≡ λ h → (John любит h в-мире w₁)
  _ = refl
  
  _ : ⟦ Чемпион ★ iЛюбит ⟧/ w₂ ≡ λ h → (Mary любит h в-мире w₂)
  _ = refl
  \end{code}
\end{frame}

\begin{frame}
  \vspace{2ex}
  \begin{code}
  _ : (⟦ Чемпион ★ iЛюбит ⟧/ w₁) John ≡
                           John любит John в-мире w₁
  _ = refl
  
  _ : (⟦ Чемпион ★ iЛюбит ⟧/ w₁) John   
  _ = lself1 John
  
  _ : (⟦ Чемпион ★ iЛюбит ⟧/ w₂) Mary → ⊥  
  _ = λ z → lself2 Mary z
  
  _ : (⟦ Чемпион ★ iЛюбит ⟧/ w₂) Bill
  _ = MlB2
  \end{code}
\end{frame}

\begin{frame}
  \vspace{2ex}
  \begin{agdacomm}
    Композиция вычислений.\\
    «Отец чемпиона бежит».
  \end{agdacomm}
  \begin{code}
  iОтец : Человек → (∧ Человек)
  iОтец h = mkIntensional (λ w → (отец h w))
    where
    отец : Человек → Мир → Человек
    отец John w₁ = Bill
    отец Mary w₁ = Bill
    отец Bill w₁ = Unknown
    отец Unknown w₁ = Unknown
    отец John w₂ = Bill
    отец Mary w₂ = John
    отец Bill w₂ = Unknown
    отец Unknown w₂ = Unknown
  \end{code}
\end{frame}

\begin{frame}
  \begin{agdacomm}
    «Отец чемпиона бежит» = {\agdafont Чемпион ★ iОтец ★ iБежит}:
  \end{agdacomm}
  \begin{code}
  _ : ⟦ Чемпион ★ iОтец ★ iБежит ⟧/ w₁ ≡ Bill бежит-в-мире w₁
  _ = refl
  
  _ : ⟦ Чемпион ★ iОтец ★ iБежит ⟧/ w₂ ≡ John бежит-в-мире w₂
  _ = refl
  
  _ : ⟦ Чемпион ★ iОтец ★ iБежит ⟧/ w₁
  _ = Br1
  \end{code}
\end{frame}

\begin{frame}[squeeze]
  \vspace{1ex}
  \begin{agdacomm}
    Рассмотрим модальную логику.\\
    Определяем отношение достижимости:
  \end{agdacomm}
  \begin{code}[hide]
  module ModalLogic where
  infix 5 _≈>_
  \end{code}
  \begin{code}
  _≈>_ : Мир → Мир → Set
  W₁ ≈> W₂ = ⊤
  \end{code}
  \begin{agdacomm}
    Миры, достижимые из некоторого мира.\\
    Здесь {\agdafont Σ[ w ∈ Мир ] P} обозначает $\tsum(w:\text{Мир}) P$.
  \end{agdacomm}
  \begin{code}
  acc : Мир → Set
  acc w₀ = Σ[ w ∈ Мир ] w₀ ≈> w
  \end{code}
  \begin{agdacomm}
    Необходимость и возможность.
  \end{agdacomm}
  \begin{code}
  □ : ∧ Set → Set
  □ P = ∀ w → ⟦ P ⟧/ w
  ◇ : ∧ Set → Set
  ◇ P = Σ[ w ∈ Мир ] ⟦ P ⟧/ w

  □' : Мир → ∧ Set → Set
  □' w₀ P = ∀ (x : acc w₀)  → ⟦ P ⟧/ (proj₁ x)
  ◇' : Мир → ∧ Set → Set
  ◇' w₀ P = Σ[ x ∈ acc w₀ ] ⟦ P ⟧/ (proj₁ x)
  \end{code}
\end{frame}

\begin{frame}
  \vspace{1ex}
  \begin{agdacomm}
    «Необходимо, что чемпион бежит».
  \end{agdacomm}
  \begin{code}
  _ : □ (Чемпион ★ iБежит) 
  _ = prf where 
    prf : (w : Мир) → ⟦ Чемпион ★ iБежит ⟧/ w 
    prf w₁ = Jr1
    prf w₂ = Mr2
  
  _ : □' w₁ (Чемпион ★ iБежит)
  _ = prf where 
    prf : (w : acc w₁) → ⟦ Чемпион ★ iБежит ⟧/ (proj₁ w) 
    prf (w₁ , _) = Jr1
    prf (w₂ , _) = Mr2
  \end{code}  
  \begin{agdacomm}
    «Возможно, что чемпион бежит».
  \end{agdacomm}
  \begin{code}
  _ : ◇ (Чемпион ★ iБежит) 
  _ = w₁ , Jr1
  
  _ : ◇' w₁ (Чемпион ★ iБежит)
  _ = (w₂ , _) , Mr2
  \end{code}
\end{frame}

\begin{frame}
  \vspace{2ex}
  \begin{agdacomm}
    Сообщения о мнении. Ральф.
  \end{agdacomm}
  \begin{code}[hide]
module Ralph where
  open import Monad.Identity
  open import Monad.Reader   
  \end{code}
  \begin{code}
  data НосительМнения : Set where 
    Ральф Мы : НосительМнения
  IntMonad = MonadReader НосительМнения
  
  ∧ : ∀ {i} → Set i → Set i
  ∧ = Reader НосительМнения
  
  mkIntensional : ∀ {i} {A : Set i} → (НосительМнения → A) → ∧ A
  mkIntensional f = mkReaderT (λ w → mkIdentity (f w))
  
  ∨ : ∀ {i} {A : Set i} → ∧ A → (НосительМнения → A)
  ∨ = runReader                 
  
  ⟦_⟧/_ : ∀ {i} {A : Set i} → ∧ A → НосительМнения → A
  ⟦ ma ⟧/ b = ∨ ma b
  
  rigid = return
  \end{code}
  \begin{code}[hide]
  infixl 5 _★_
  _★_ = _>>=_
  \end{code}
\end{frame}

\begin{frame}
  \vspace{2ex}
  \begin{code}
  data Человек : Set where
    чел-в-шляпе чел-на-пляже Орткут : Человек
  
  xh : ∧ Человек
  xh = mkIntensional f
    where
    f : НосительМнения → Человек
    f Ральф = чел-в-шляпе
    f Мы = Орткут
  
  xb : ∧ Человек
  xb = mkIntensional f
    where
    f : НосительМнения → Человек
    f Ральф = чел-на-пляже
    f Мы = Орткут
  \end{code}
\end{frame}

\begin{frame}
  \vspace{1ex}
  \begin{code}
  postulate
    _считает-что_шпион : НосительМнения → Человек → Set
    spyh : Ральф считает-что чел-в-шляпе шпион
    spyb : Ральф считает-что чел-на-пляже шпион → ⊥
  \end{code}
  \begin{code}[hide]
  _считаем-что_шпион = _считает-что_шпион
  \end{code}
  \begin{code}
  iСчитает-шпионом : Человек → (∧ Set)
  iСчитает-шпионом h =
          mkIntensional (λ b → b считает-что h шпион)
  
  _ : ⟦ xh ★ iСчитает-шпионом ⟧/ Ральф ≡
                           Ральф считает-что чел-в-шляпе шпион
  _ = refl
  
  _ : ⟦ xh ★ iСчитает-шпионом ⟧/ Ральф
  _ = spyh
  
  _ : ⟦ xb ★ iСчитает-шпионом ⟧/ Ральф → ⊥
  _ = spyb
  \end{code}
\end{frame}

\begin{frame}
  \vspace{2ex}
  \begin{code}
  _ : ⟦ rigid Орткут ★ iСчитает-шпионом ⟧/ Мы ≡
                            Мы считаем-что Орткут шпион
  _ = refl
  
  _ : ⟦ rigid Орткут ★ iСчитает-шпионом ⟧/ Ральф ≡
                            Ральф считает-что Орткут шпион
  _ = refl
  \end{code}
  \begin{code}[hide]
  postulate
  \end{code}
  Невозможно доказать, что
  \begin{code}
    _ : ⟦ rigid Орткут ★ iСчитает-шпионом ⟧/ Ральф
  \end{code}
\end{frame}

\begin{frame}[label=finalslide,standout]
  Спасибо за внимание\,!
\end{frame}

\end{document}
