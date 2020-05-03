; Cours 02 : Fonctions
; Yann MARTIN D'ESCRIENNE

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  ;[plusE (l : Exp) (r : Exp)]
  [plusE (Ladd : (Listof Exp))]
  [moinsE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [appE (fun : Symbol) (Larg : (Listof Exp))])

; Représentation des définitions de fonctions
(define-type FunDef
  [fd (name : Symbol) (Lpar : (Listof Symbol)) (body : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ...} s)
     (let ([sl (s-exp->list s)])
       (plusE (map parse (rest sl))))]
    [(s-exp-match? `{- ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (moinsE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{SYMBOL ANY ...} s)
     (let ([sl (s-exp->list s)])
       (appE (s-exp->symbol (first sl)) (map parse (rest sl))))]
    [else (error 'parse "invalid input")]))

(define (parse-fundef [s : S-Exp]) : FunDef
  (if (s-exp-match? `{define {SYMBOL SYMBOL ...} ANY} s)
      (let ([sl (s-exp->list s)])
        (let* ([sl2 (s-exp->list (second sl))]
              [Lpar (map s-exp->symbol (rest sl2))])
          (if (repetion Lpar)
              (error 'parse-fundef "bad syntax")
              (fd (s-exp->symbol (first sl2)) 
                  Lpar
                  (parse (third sl))))))
      (error 'parse-fundef "invalid input")))

(define (repetion [L : (Listof Symbol)]) : Boolean
  (cond
    [(empty? L) #f]
    [(member (first L) (rest L)) #t]
    [else (repetion (rest L))]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;


; Interpréteur
(define (interp [e : Exp] [fds : (Listof FunDef)]) : Number
  (type-case Exp e
    [(numE n) n]
    [(idE s) (error 'interp "free identifier")]
    [(plusE Ladd) (foldl + 0 (map (lambda ([x : Exp]) (interp x fds)) Ladd))]
    [(multE l r) (* (interp l fds) (interp r fds))]
    [(moinsE l r) (- (interp l fds) (interp r fds))]
    [(appE f Larg) (let [(fd (get-fundef f fds))]
                     (interp (substForAll Larg (fd-Lpar fd) (fd-body fd) fds)
                             fds))]))

(define (substForAll [Larg : (Listof Exp)] [Lpar : (Listof Symbol)] [body : Exp] [fds : (Listof FunDef)]) : Exp
  (cond
    [(and (empty? Larg) (empty? Lpar)) body]
    [(and (cons? Larg) (cons? Lpar))
     (substForAll (rest Larg)
                  (rest Lpar)
                  (subst (numE (interp (first Larg) fds)) (first Lpar) body)
                  fds)]
    [else (error 'substForAll "wrong arity")]))

; Recherche d'une fonction parmi les définitions
(define (get-fundef [s : Symbol] [fds : (Listof FunDef)]) : FunDef
  (cond
    [(empty? fds) (error 'get-fundef "undefined function")]
    [(equal? s (fd-name (first fds))) (first fds)]
    [else (get-fundef s (rest fds))]))

; Substitution
(define (subst [what : Exp] [for : Symbol] [in : Exp]) : Exp
  (type-case Exp in
    [(numE n) in]
    [(idE s) (if (equal? for s) what in)]
    [(plusE Ladd) (plusE (map (lambda ([x : Exp]) (subst what for x)) Ladd))]
    [(moinsE l r) (moinsE (subst what for l) (subst what for r))]
    [(multE l r) (multE (subst what for l) (subst what for r))]
    [(appE f Larg) (appE f (map (lambda ([x : Exp]) (subst what for x)) Larg))]))
;[(appE f Larg) (numE 0)]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp] [fds : (Listof S-Exp)]) : Number
  (interp (parse e) (map parse-fundef fds)))


;(test (interp-expr `{double 3}
;                   (list `{define {double x} {+ x x}}))
;      6)
;
;(test (interp-expr `{quadruple 3}
;                   (list `{define {double x} {+ x x}}
;                         `{define {quadruple x} {double {double x}}}))
;      12)
;
;(test (interp-expr `{- 1 2} empty) -1)
;(test (interp-expr `{- {- 8 2} 5} empty) 1)
;
;(test (interp-expr `{+} empty) 0)
;(test (interp-expr `{+ 1 } empty) 1)
;(test (interp-expr `{+ 1 2} empty) 3)
;(test (interp-expr `{+ 1 2 3 4 5} empty) 15)
;
;(test (interp-expr `{f 1 2}
;                   (list `{define {f x y} {+ x y}}))
;      3)
;(test (interp-expr `{g {f} 5}
;                   (list `{define {f} 3} `{define {g x y} {+ {+ x x} y}}))
;      11)
;
;(test (interp-expr `{+ {f} {f} }
;                   (list `{define {f} 5}))
;      10)
;
;(test/exn (interp-expr `{f 1}
;                       (list `{define {f x y} {+ x y}}))
;          "wrong arity")
;
;(test/exn (interp-expr `{f 1 2 3}
;                       (list `{define {f x y} {+ x y}}))
;          "wrong arity")
;
;( test/exn ( interp-expr `{f 1 2} ( list `{ define {f x x} {+ x x} })) "bad syntax")
;( test/exn ( interp-expr `{f 1 2 3 4} ( list `{ define {f x y z x} {+ x x} })) "bad syntax")
;( test/exn ( interp-expr `{f 1 2 3 4} ( list `{ define {f x y z x y} {+ x x} })) "bad syntax")