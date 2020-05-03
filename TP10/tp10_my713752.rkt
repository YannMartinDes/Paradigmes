; Cours 10 : Types

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (par-type : Type) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]

  [boolE (s : Boolean)]
  [ifE (cond : Exp) (do : Exp) (elseCase : Exp)]
  [egalE (l : Exp) (r : Exp)]

  [pairE (fst : Exp) (snd : Exp)]
  [fstE (pair : Exp)]
  [sndE (pair : Exp)]

  [letrecE (sym : Symbol) (type : Type) (rhs : Exp) (body : Exp)]
  )

; Représentation du type des expressions
(define-type Type
  [numT]
  [boolT]
  [arrowT (par : Type) (res : Type)]  
  [prodT (l : Type) (r : Type)])
   
; Représentation des liaisons identificateurs type
(define-type TypeBinding
  [tbind (name : Symbol) (type : Type)])

; Environnement pour les types
(define-type-alias TypeEnv (Listof TypeBinding))

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [boolV (b : Boolean)]
  [closV (arg : Symbol) (body : Exp) (env : Env)]
  [pairV (fst : Exp) (snd : Exp)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : (-> Value))])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    
    [(s-exp-match? `true s) (boolE #t)];Mettre avant sinon catch par idE
    [(s-exp-match? `false s) (boolE #f)]

    [(s-exp-match? `{= ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (egalE (parse (second sl)) (parse (third sl))))]
    
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (third (rest sl)))))]

    [(s-exp-match? `{pair ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (pairE (parse (second sl)) (parse (third sl))))]

    [(s-exp-match? `{fst ANY} s)
     (let ([sl (s-exp->list s)])
       (fstE (parse (second sl))))]

    [(s-exp-match? `{snd ANY} s)
     (let ([sl (s-exp->list s)])
       (sndE (parse (second sl))))]

    [(s-exp-match? `{letrec {[SYMBOL : ANY ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (letrecE (s-exp->symbol (first sll))
                  (parse-type (third sll))
                  (parse (fourth sll))
                  (parse (third sl)))))]
    
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {[SYMBOL : ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (lamE (s-exp->symbol (first sll))
               (parse-type (third sll))
               (parse (third sl)))))]
    [(s-exp-match? `{let {[SYMBOL : ANY ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (appE
          (lamE (s-exp->symbol (first sll))
                (parse-type (third sll))
                (parse (third sl)))
          (parse (fourth sll)))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

(define (parse-type [s : S-Exp]) : Type
  (cond
    [(s-exp-match? `num s) (numT)]
    [(s-exp-match? `bool s) (boolT)]
    [(s-exp-match? `(ANY -> ANY) s)
     (let ([sl (s-exp->list s)])
       (arrowT (parse-type (first sl))
               (parse-type (third sl))))]
    [(s-exp-match? `(ANY * ANY) s)
     (let ([sl (s-exp->list s)])
       (prodT (parse-type (first sl)) (parse-type (third sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Vérification des types ;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (typecheck [e : Exp] [env : TypeEnv]) : Type
  (type-case Exp e
    [(numE n) (numT)]
    [(idE s) (type-lookup s env)]
    [(plusE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(multE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(lamE par par-type body)
     (arrowT par-type
             (typecheck body
                        (extend-env (tbind par par-type) env)))]
    [(appE fun arg)
     (let ([t1 (typecheck fun env)]
           [t2 (typecheck arg env)])
       (type-case Type t1
         [(arrowT par-type res-type)
          (if (equal? par-type t2)
              res-type
              (type-error arg par-type t2))]
         [else (type-error-function fun t1)]))]

    
    [(boolE b) (boolT)]
    [(egalE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (boolT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    
    [(ifE cond do elsecase)
     (let ([t1 (typecheck cond env)]
           [t2 (typecheck do env)]
           [t3 (typecheck elsecase env)])
       (type-case Type t1
         [(boolT) (if (equal? t2 t3) t2
                      (type-error elsecase t2 t3))]
         [else (type-error cond (boolT) t1)]))]


    [(pairE fst snd)
     (let ([t1 (typecheck fst env)]
           [t2 (typecheck snd env)])
       (prodT t1 t2))]

    [(fstE pair)
     (let ([t1 (typecheck pair env)])
       (type-case Type t1
         [(prodT t2 t3) t2]
         [else (type-error-product pair t1)]))]
    
    [(sndE pair)
     (let ([t1 (typecheck pair env)])
       (type-case Type t1
         [(prodT t2 t3) t3]
         [else (type-error-product pair t1)]))]

    [(letrecE s type rhs body)
     (let ([t1 (typecheck rhs (extend-env (tbind s type) env))])
       (if (equal? type t1)
           (typecheck body (extend-env (tbind s type) env))
           (type-error rhs type t1)))]

    ))

; Concaténation de chaînes de caractères
(define (cat [strings : (Listof String)]) : String
  (foldr string-append "" strings))

; Message d'erreur
(define (type-error [expr : Exp] [expected-type : Type] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected type " (to-string expected-type)
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-function [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected function "
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-product [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected product "
                               ", found type " (to-string found-type)))))

; Recherche d'un identificateur dans l'environnement
(define (type-lookup [s : Symbol] [env : TypeEnv]) : Type
  (cond
    [(empty? env) (error 'typecheck "free identifier")]
    [(equal? s (tbind-name (first env))) (tbind-type (first env))]
    [else (type-lookup s (rest env))]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(idE s) (lookup s env)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(lamE par par-type body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (lambda () (interp arg env))) c-env))]
       [else (error 'interp "not a function")])]

    [(boolE b) (boolV b)]
    [(egalE l r) (num= (interp l env) (interp r env))]
    [(ifE cond do elseCase) (interpIf (interp cond env) do elseCase env)]

    [(pairE fst snd) (pairV fst snd)]

    [(fstE pair)
     (type-case Value (interp pair env)
       [(pairV fst snd)
        (interp fst env)]
       [else (error 'interp "not a pair")])]
    
    [(sndE pair)
     (type-case Value (interp pair env)
       [(pairV fst snd)
        (interp snd env)]
       [else (error 'interp "not a pair")])]

    [(letrecE s type rhs body)
     (letrec ([new-env (extend-env (bind s (lambda () val)) env)]
              [val (interp rhs new-env)])
       (interp body new-env))]
    ))

; Recherche d'un identificateur dans l'environnement
(define (lookup [s : Symbol]
                [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) ((bind-val (first env)))]
    [else (lookup s (rest env))]))

; Vérification des types pour les opérations arithmétiques
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

; Spécialisation de num-op pour l'addition
(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

; Spécialisation de num-op pour la multiplication
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

(define (num= [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (boolV (= (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (interpIf [cond : Value] [do : Exp] [elseCase : Exp] [env : Env]) : Value
  (if (boolV? cond)
      (if (equal? (boolV-b cond) #t)
          (interp do env)
          (interp elseCase env))
      (error 'interp "not a boolean")))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (let ([expr (parse e)])
    (begin
      (typecheck expr mt-env)
      (interp expr mt-env))))

(define (typecheck-expr [e : S-Exp]) : Type
  (typecheck (parse e) mt-env))


(define (interp-expr2 [e : S-Exp]) : Value
  (interp (parse e) mt-env))

(test (typecheck-expr `{lambda {[x : (num * bool)]} {fst x} })
      (arrowT ( prodT ( numT ) ( boolT )) ( numT )))


