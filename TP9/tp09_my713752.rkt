; Cours 09 : Classes

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des classes (langage utilisateur)
(define-type ClassS
  [classS (super-name : Symbol)
          (field-names : (Listof Symbol))
          (methods : (Listof (Symbol * ExpS)))])

; Représentation des expressions (langage utilisateur)
(define-type ExpS
  [thisS]
  [argS]
  [numS (n : Number)]
  [plusS (l : ExpS) (r : ExpS)]
  [multS (l : ExpS) (r : ExpS)]
  [newS (class : Symbol) (field-values : (Listof ExpS))]
  [getS (object : ExpS) (field : Symbol)]
  [sendS (object : ExpS) (method : Symbol) (arg : ExpS)]
  [superS (method : Symbol) (arg : ExpS)]
  [selectS (n : ExpS) (obj : ExpS) (arg : ExpS)]
  [instanceofS (expr : ExpS) (inst : Symbol)]
  )

; Représentation des classes (langage interne)
(define-type Class
  [classE (field-names : (Listof Symbol))
          (methods : (Listof (Symbol * Exp)))
          (super-name : Symbol)])

; Représentation des expressions (langage interne)
(define-type Exp
  [thisE]
  [argE]
  [numE (n : Number)]
  ;[plusE (l : Exp) (r : Exp)]
  ;[multE (l : Exp) (r : Exp)]
  [newE (class : Symbol) (field-values : (Listof Exp))]
  [getE (object : Exp) (field : Symbol)]
  [sendE (object : Exp) (method : Symbol) (arg : Exp)]
  [ssendE (object : Exp) (class : Symbol) (method : Symbol) (arg : Exp)]
  [selectE (n : Exp) (obj : Exp) (arg : Exp)]
  [instanceofE (expr : Exp) (inst : Symbol)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [objV (class-name : Symbol)
        (field-values : (Listof Value))])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

; Analyse d'une classe
(define (parse-class [s : S-Exp]) : (Symbol * ClassS)
  (cond
    [(s-exp-match? `{class SYMBOL extends SYMBOL
                      {SYMBOL ...}
                      {SYMBOL ANY} ...} s)
     (let ([sl (s-exp->list s)])
       (let ([mtds (rest (rest (rest (rest (rest sl)))))])
         (pair
          (s-exp->symbol (second sl))
          (classS
           (s-exp->symbol (fourth sl))
           (map s-exp->symbol (s-exp->list (list-ref sl 4)))
           (map (lambda (mtd)
                  (let ([mtdl (s-exp->list mtd)])
                    (pair (s-exp->symbol (first mtdl))
                          (parse (second mtdl) #t))))
                mtds)))))]
    [else (error 'parse-class "invalid input")]))

; Analyse des expressions
(define (parse [s : S-Exp] [in-method : Boolean]) : ExpS
  (local [(define (parse-r s) (parse s in-method))]
    (cond
      [(s-exp-match? `arg s) (if in-method (argS) (error 'parse "invalid input"))]
      [(s-exp-match? `this s) (if in-method (thisS) (error 'parse "invalid input"))]
      [(s-exp-match? `NUMBER s) (numS (s-exp->number s))]
      [(s-exp-match? `{+ ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (plusS (parse-r (second sl)) (parse-r (third sl))))]
      [(s-exp-match? `{* ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (multS (parse-r (second sl)) (parse-r (third sl))))]
      [(s-exp-match? `{new SYMBOL ANY ...} s)
       (let ([sl (s-exp->list s)])
         (newS (s-exp->symbol (second sl)) (map parse-r (rest (rest sl)))))]
      [(s-exp-match? `{get ANY SYMBOL} s)
       (let ([sl (s-exp->list s)])
         (getS (parse-r (second sl)) (s-exp->symbol (third sl))))]
      [(s-exp-match? `{send ANY SYMBOL ANY} s)
       (let ([sl (s-exp->list s)])
         (sendS (parse-r (second sl)) (s-exp->symbol (third sl)) (parse-r (fourth sl))))]
      [(s-exp-match? `{super SYMBOL ANY} s)
       (let ([sl (s-exp->list s)])
         (superS (s-exp->symbol (second sl)) (parse-r (third sl))))]
     
     
      [(s-exp-match? `{select ANY ANY ANY} s)
       (let ([sl (s-exp->list s)])
         (selectS (parse-r (second sl)) (parse-r (third sl)) (parse-r (fourth sl))))]
      [(s-exp-match? `{instanceof ANY SYMBOL} s)
       (let ([sl (s-exp->list s)])
         (instanceofS (parse-r (second sl)) (s-exp->symbol (third sl))))]
      
      [else (error 'parse "invalid input")])))

;;;;;;;;;;;;;;;
; Compilation ;
;;;;;;;;;;;;;;;

; passage d'une expression utilisateur en expression interne
(define (exp-s->e [e : ExpS] [super-name : Symbol]) : Exp
  (let ([aux (lambda (e) (exp-s->e e super-name))])
    (type-case ExpS e
      [(thisS) (thisE)]
      [(argS) (argE)]
      [(numS n) (numE n)]
      [(plusS l r) (sendE (aux l) 'plus (aux r))]
      [(multS l r) (sendE (aux l) 'mult (aux r))]
      [(newS c fd-vals) (newE c (map aux fd-vals))]
      [(getS o fd) (getE (aux o) fd)]
      [(sendS o mtd arg) (sendE (aux o) mtd (aux arg))]
      [(superS mtd arg) (ssendE (thisE) super-name mtd (aux arg))]
      [(selectS n obj arg) (selectE (aux n) (aux obj) (aux arg))]
      [(instanceofS expr inst) (instanceofE (aux expr) inst)])))

; passage d'une classe utilisateur en classe interne
(define (class-s->e [c : (Symbol * ClassS)]) : (Symbol * Class)
  (type-case ClassS (snd c)
    [(classS super-name fds mtds)
     (pair (fst c)
           (classE fds
                   (map (lambda (mtd)
                          (pair (fst mtd) (exp-s->e (snd mtd) super-name)))
                        mtds)
                   super-name))]))

; compilation d'une classe utilisateur brute
(define (compile-class
         [raw : (Symbol * ClassS)]
         [compiled : (Listof (Symbol * ClassS))]) : (Listof (Symbol * ClassS))
  (type-case ClassS (snd raw)
    [(classS super-name fds mtds)
     (type-case ClassS (find super-name compiled)
       [(classS super-super-name super-fds super-mtds)
        (let ([c (classS super-name
                         (merge-fields fds super-fds)
                         (merge-methods mtds super-mtds))])
          (cons (pair (fst raw) c) compiled))])]))

; fusion des champs
(define (merge-fields fds super-fds) (append super-fds fds))

; fusion des méthodes
(define (merge-methods mtds super-mtds)
  (let* ([defined (map fst mtds)]
         [super-defined (map fst super-mtds)]
         [not-redefined (filter (lambda (mtd-name)
                                  (not (member mtd-name defined)))
                                super-defined)]
         [inherited-mtds (map (lambda (mtd-name)
                                (pair mtd-name (superS mtd-name (argS))))
                              not-redefined)])
    (append mtds inherited-mtds)))

; tri topologique
(define (topological-sort
         [from : (Symbol * ClassS)]
         [classes : (Listof (Symbol * ClassS))])
  : (Listof (Symbol * ClassS))
  (let* ([children
          (filter (lambda (c)
                    (equal? (classS-super-name (snd c))
                            (fst from)))
                  classes)]
         [children-lists
          (map (lambda (child) (topological-sort child classes))
               children)])
    (cons from (foldl append empty children-lists))))

; compilation des classes utilisateur brutes
(define (compile-classes
         [raws : (Listof (Symbol * ClassS))]) : (Listof (Symbol * Class))
  (let* ([sorted (topological-sort
                  (pair 'Object (classS 'Object empty empty))
                  raws)]
         [compiled (foldl compile-class
                          (list (first sorted)) ; Object pré-compilé
                          (rest sorted))])
    (map class-s->e compiled)))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [classes : (Listof (Symbol * Class))]
                [this-v : Value] [arg-v : Value]) : Value
  (let ([interp-r (lambda (e) (interp e classes this-v arg-v))])
    (type-case Exp e
      [(thisE) this-v]
      [(argE) arg-v]
      [(numE n) (numV n)]
      ;[(plusE l r) (num+ (interp-r l) (interp-r r))]
      ;[(multE l r) (num* (interp-r l) (interp-r r))]
      [(newE class-name fd-exprs)
       (let ([c (find class-name classes)])
         (if (= (length fd-exprs) (length (classE-field-names c)))
             (objV class-name (map interp-r fd-exprs))
             (error 'interp "wrong fields count")))]
      [(getE obj fd)
       (type-case Value (interp-r obj)
         [(objV class-name fd-vals)
          (let ([c (find class-name classes)])
            (find fd (map2 pair
                           (classE-field-names c)
                           fd-vals)))]
         [else (error 'interp "not an object")])]
      [(sendE obj mtd arg)
       (let ([obj-v (interp-r obj)])
         (type-case Value obj-v
           [(objV class-name fd-vals)
            (call-method class-name mtd classes obj-v (interp-r arg))]
           [(numV l)
            (cond
              [(equal? mtd 'plus) (num+ obj-v (interp-r arg))]
              [(equal? mtd 'mult) (num* obj-v (interp-r arg))]
              [else (error 'interp "not found")])]
           ;[else (error 'interp "not an object")]
           ))]
      [(ssendE obj class-name mtd arg)
       (call-method class-name mtd classes (interp-r obj) (interp-r arg))]

      [(selectE n obj arg)
       (let ([obj-v (interp-r obj)])
         (type-case Value obj-v
           [(objV class-name fd-vals)
            (type-case Value (interp-r n)
              [(numV v) (if (= v 0)
                            (call-method class-name 'select-false classes obj-v (interp-r arg))
                            (call-method class-name 'select-true classes obj-v (interp-r arg)))]
              [else (error 'interp "not a number")])]
           [else (error 'interp "not an object")]))]

      [(instanceofE expr inst)
       (type-case Value (interp-r expr)
         [(objV class-name fd-vals)
          (instanceof-rec class-name classes inst)]
         [else (error 'interp "not an object")])
       ]
      )))


;TP-------------------------
(define (instanceof-rec [class-name : Symbol] [classes : (Listof (Symbol * Class))] [inst : Symbol]) : Value
  (cond
    [(equal? class-name 'Object) (numV 0)]
    [(equal? class-name inst) (numV 1)]
    [else
     (type-case Class (find class-name classes)
       [(classE field-names methods super-name)
        (instanceof-rec super-name classes inst)])]
    ))


; Fonctions utilitaires pour l'arithmétique
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

; Recherche dans des listes d'association
(define (find [name : Symbol]
              [pairs : (Listof (Symbol * 'a))]) : 'a
  (cond
    [(empty? pairs) (error 'find "not found")]
    [(equal? name (fst (first pairs))) (snd (first pairs))]
    [else (find name (rest pairs))]))

; Appel de méthode
(define (call-method [class-name : Symbol]
                     [method-name : Symbol]
                     [classes : (Listof (Symbol * Class))]
                     [this-v : Value]
                     [arg-v : Value]) : Value
  (type-case Class (find class-name classes)
    [(classE field-names methods super-name)
     (interp (find method-name methods) classes this-v arg-v)]))


;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [expr : S-Exp] [classes : (Listof S-Exp)])
  (interp (exp-s->e (parse expr #f) 'Object)
          (compile-classes (map parse-class classes))
          (objV 'Object empty)
          (numV 0)))

(define Posn-class
  `{class Posn extends Object
     {x y}
     [dist {+ {get this x} {get this y}}]
     [addDist {+ {send this dist 0}
                 {send arg dist 0}}]})

(define Posn3D-class
  `{class Posn3D extends Posn
     {z}
     [dist {+ {get this z} {super dist arg}}]})

(define (interp-posn e)
  (interp-expr e (list Posn-class Posn3D-class)))

(test (interp-posn `{send {new Posn 1 2}
                          dist
                          0})
      (numV 3))

(test (interp-posn `{send {new Posn3D 3 4 5}
                          addDist
                          {new Posn 1 2}})
      (numV 15))

(test (interp-expr `{instanceof {new Triple 1 2 3} Singleton}
                   (list `{class Singleton extends Object {x}}
                         `{class Pair extends Singleton {y}}
                         `{class Triple extends Pair {z}}))
      (numV 1))

(test (interp-expr `{instanceof {new Pair 1 2} Triple}
                   (list `{class Singleton extends Object {x}}
                         `{class Pair extends Singleton {y}}
                         `{class Triple extends Pair {z}}))
      (numV 0))

(test/exn (interp-expr `{instanceof 3 Triple}
                       (list `{class Singleton extends Object {x}}
                             `{class Pair extends Singleton {y}}
                             `{class Triple extends Pair {z}}))
          "not an object")

(test (interp-expr `{send 1 plus 2} empty) (numV 3))

(test (interp-expr `{send 1 mult 2} empty) (numV 2))

(test (interp-expr `{* 6 3} empty) (numV 18))

(test (interp-expr `{send 1 mult (* 2 3)} empty) (numV 6))

(test/exn (interp-expr `{send 1 div 2} empty) "not found")

(test (interp-expr `{send {+ 1 2} ; <=> {+ {+ 1 2} {* {* 3 4} 5}}
                          plus
                          {send {* 3 4}
                                mult
                                5}}
                   empty)
      (numV 63))

