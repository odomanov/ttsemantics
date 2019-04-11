% -*- mode: LaTeX; coding: utf-8 -*-
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{mybeamer}[2019/03/19 My beamer setup]

\RequirePackage{etoolbox}

%
% ==== Options ====
%
% \newtoggle{badioubook@draftprint}
% \togglefalse{badioubook@draftprint}
% \DeclareOption{draftprint}{\toggletrue{badioubook@draftprint}}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{beamer}}

\ProcessOptions*\relax

\LoadClass{beamer}

\RequirePackage[english,russian]{babel}
% \RequirePackage{graphicx}
% \RequirePackage{longtable}
\RequirePackage{amsmath}
\RequirePackage{textcomp}
\RequirePackage{amssymb}
\RequirePackage{booktabs}
\RequirePackage{tabu}
\RequirePackage{etoolbox}
\RequirePackage[babel,style=russian,threshold=3]{csquotes}
  \MakeAutoQuote{«}{»}
  \setquotestyle*
% \RequirePackage{indentfirst}
% \RequirePackage{microtype}
\RequirePackage{makebox} %\makebox*[2] command
\RequirePackage{hyperref}
  \hypersetup{unicode=true,pdfusetitle,raiselinks,bookmarks=true}
  \hypersetup{bookmarksnumbered=true,bookmarksopen=true,bookmarksopenlevel=4}
  \hypersetup{breaklinks=true,pdfborder={0 0 0},backref=false}
  \hypersetup{colorlinks=true,pdfstartview=FitH,allcolors=blue}
% \hypersetup{
%  pdfauthor={Oleg Domanov},
%  pdftitle={Type-Theoretic Semantics},
%  pdfkeywords={},
%  pdfsubject={},
%  pdflang={English}}


\tolerance=1000
\RequirePackage{mathtools}
% \RequirePackage{tikz}
% \tikzstyle{every picture}+=[remember picture]

\newcommand{\sentence}[1]{\textcolor{orange}{#1}}
\usetheme[numbering=none,
progressbar=frametitle,
titleformat=smallcaps
]{metropolis}
\setsansfont[BoldFont={Fira Sans SemiBold}]{Fira Sans Book}
\setbeamercolor{head}{bg=lightgray!70!white}
\setbeamercolor{body}{bg=lightgray!30!white}
\setbeamertemplate{itemize item}[default]
\setbeamerfont{itemize item}{size=\tiny}
\setbeamertemplate{itemize subitem}[ball]

\newcommand*{\pair}[1]{\left\langle #1\right\rangle}
%for Heyting algebras
\newcommand*{\hneg}{\neg}%\righthalfcap}   % negation
\newcommand*{\himpl}{\Rightarrow}    % implication
\newcommand*{\proves}{\vdash}
\newcommand{\tsum}{\Sigma}%{\mbox{\large $\Sigma$}}%{\textstyle\sum}
\newcommand{\tprod}{\Pi}%{\mbox{\large $\Pi$}}%{\textstyle\prod}
\newcommand{\is}{\!:\!}
\RequirePackage{lmake}
%\newcommand*{\beq}[1]{\ensuremath{[\![#1]\!]}}
%\newcommand*{\beq}[1]{[[#1]]}
\DeclarePairedDelimiter{\beq}{[\![}{]\!]}
% \DeclarePairedDelimiter{\beq}{\llbracket}{\rrbracket}  % stmaryrd
% \DeclarePairedDelimiter{\beq}{\lBrack}{\rBrack}  % unicode-math xe/lua

\RequirePackage[math-style=ISO,bold-style=ISO%,vargreek-shape=unicode
]{unicode-math}       

\setmathfont{STIX Two Math}[Scale=MatchLowercase] %no
% \setmathfont{XITS Math}
% \setmathfont{Latin Modern Math}
% \setmathfont[range={\mathcal,\mathbfcal},StylisticSet=1]{XITS Math}
% \setmathfont[range=\mathscr]{XITS Math}
% \setmathfont{TeX Gyre Bonum Math}
% \setmathfont{TeX Gyre Schola Math}
% \setmathfont[range=\mathscr]{TeX Gyre Bonum Math}
% \setmathfont{Fira Sans Book}
% \setmathfont[range={\mathcal,\mathbfcal},StylisticSet=1]{XITS Math}
% \setmathfont[range=\mathscr,StylisticSet=1]{XITS Math}

\endinput
