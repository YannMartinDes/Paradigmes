; Cours 06 : Interpréteur pour le lambda-calcul à compléter

#lang plait

;;;;;;;;;;;;;;;
; Expressions ;
;;;;;;;;;;;;;;;

; Langage intermédiaire
(define-type ExpS
  [idS (s : Symbol)]
  [lamS (pars : (Listof Symbol)) (body : ExpS)]
  [appS (fun : ExpS) (args : (Listof ExpS))]
  [letS (pars : (Listof Symbol)) (args : (Listof ExpS)) (body : ExpS)]

  [numS (n : Number)]
  [add1S]
  [plusS]
  [multS]

  [trueS]
  [falseS]
  [ifS (cnd : ExpS) (l : ExpS) (r : ExpS)]  
  [zeroS]

  [pairS]
  [fstS]
  [sndS]
  [sub1S]
  [minusS]
  
  [divS]
 
  [letrecS (par : Symbol) (arg : ExpS) (body : ExpS)])

; Le langage du lambda-calcul
(define-type Exp
  [idE (s : Symbol)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (compose f g)
  (lambda (x) (f (g x))))

(define (parse [s : S-Exp]) : ExpS
  (cond
    [(s-exp-match? `NUMBER s) (numS (s-exp->number s))]

    ; ensembles de symboles prédéfinis
    [(s-exp-match? `add1 s) (add1S)]
    [(s-exp-match? `+ s) (plusS)]
    [(s-exp-match? `sub1 s) (sub1S)]
    [(s-exp-match? `- s) (minusS)]
    [(s-exp-match? `* s) (multS)]
    [(s-exp-match? `/ s) (divS)]
    [(s-exp-match? `true s) (trueS)]
    [(s-exp-match? `false s) (falseS)]
    [(s-exp-match? `zero? s) (zeroS)]
    [(s-exp-match? `pair s) (pairS)]
    [(s-exp-match? `fst s) (fstS)]
    [(s-exp-match? `snd s) (sndS)]
    
    [(s-exp-match? `SYMBOL s) (idS (s-exp->symbol s))]
    [(s-exp-match? `{lambda {SYMBOL SYMBOL ...} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamS (map s-exp->symbol (s-exp->list (second sl))) (parse (third sl))))]
    [(s-exp-match? `{let {[SYMBOL ANY] [SYMBOL ANY] ...} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([substs (map s-exp->list (s-exp->list (second sl)))])
         (letS (map (compose s-exp->symbol first) substs)
               (map (compose parse second) substs)
               (parse (third sl)))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{letrec {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([substs (s-exp->list (first (s-exp->list (second sl))))])
         (letrecS (s-exp->symbol (first substs))
                  (parse (second substs))
                  (parse (third sl)))))]  
    [(s-exp-match? `{ANY ANY ANY ...} s)
     (let ([sl (s-exp->list s)])
       (appS (parse (first sl)) (map parse (rest sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Retrait du sucre syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (desugar [e : ExpS]) : Exp
  (type-case ExpS e
    [(idS s) (idE s)]
    [(lamS pars body) (if (= (length pars) 1)
                          (lamE (first pars) (desugar body))
                          (recLamS pars body)
                          ;(error 'desugar "not implemented")
                          )]
    [(appS fun args) (if (= (length args) 1)
                         (appE (desugar fun) (desugar (first args)))
                         (recAppS (desugar fun) args)
                         ;(error 'desugar "not implemented")
                         )]
    [(letS pars args body) (desugar (appS (lamS pars body) args))]
    
    [(numS n)
     (desugar (lamS (list 'f 'x)
                    (recNumS n)))]
    [(add1S)
     (desugar (lamS (list 'n 'f 'x)
                    (appS (idS 'f) ;la faut ecrire (n f x) 
                          (list
                           (appS (idS 'n)
                                 (list (idS 'f) (idS 'x))))
                          )))]

    [(plusS)
     (desugar (lamS (list 'n 'm)
                    (appS (idS 'm)
                          (list (add1S) (idS 'n))))
              )]

    [(multS)
     (desugar (lamS (list 'n 'm)
                    (appS (idS 'm)
                          (list
                           (appS (plusS)
                                 (list (idS 'n)))
                           (numS 0)))))]
    [(trueS)
     (desugar (lamS (list 'x 'y)
                    (idS 'x)))]
    [(falseS)
     (desugar (lamS (list 'x 'y)
                    (idS 'y)))]

    [(ifS cnd l r)
     (desugar (appS (appS cnd
                          (list (lamS (list 'd) l)
                                (lamS (list 'd) r)))
                    ;Argument arbitraire
                    (list (numS 0))))]

    [(zeroS)
     (desugar (lamS (list 'n)
                    (appS (idS 'n)
                          (list
                           (lamS (list 'x)
                                 (falseS))
                           (trueS)))))]

    [(pairS)
     (desugar (lamS (list 'x 'y 'sel)
                    (appS (idS 'sel)
                          (list (idS 'x) (idS 'y)))))]

    [(fstS)
     (desugar (lamS (list 'p)
                    (appS (idS 'p)
                          (list (trueS)))))]
    [(sndS)
     (desugar (lamS (list 'p)
                    (appS (idS 'p)
                          (list (falseS)))))]


    [(sub1S)
     (desugar (lamS (list 'n)
                    (appS (fstS)
                          (list
                           (appS (idS 'n)
                                 (list
                                  ;;;;;;;;; ;LE FAMEUX SHIFT ;;;;;;;;;;;;;;;;;;;;;;;
                                  (lamS (list 'p)
                                        (appS (pairS)
                                              (list
                                               (appS (sndS)
                                                     (list (idS 'p)))
                                               (appS (add1S)
                                                     (list
                                                      (appS (sndS)
                                                            (list (idS 'p))))))))
                                  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
                                  (appS (pairS)
                                        (list
                                         (numS 0) (numS 0)))
                                  ))))))]

    [(minusS)
     (desugar (lamS (list 'n 'm)
                    (appS (idS 'm)
                          (list (sub1S) (idS 'n)))))]

    [(divS)
     (desugar (lamS (list 'm 'n)
                    (divInter (idS 'm) (idS 'n) )))]

    [(letrecS name rhs body)
     (desugar
      (letS (list name)
            (list (appS (lamS (list 'bodyproc)
                              (letS (list 'fX)
                                    (list (lamS (list 'f)
                                                (letS (list name)
                                                      (list (lamS (list 'x)
                                                                  (appS
                                                                   (appS (idS 'f)
                                                                         (list (idS 'f)))
                                                                   (list (idS 'x)))))
                                                      (appS (idS 'bodyproc) (list (idS name))))))
                                    (appS (idS 'fX) (list (idS 'fX)))))
                        (list (lamS (list name) rhs))))
            body))]
                                  
    ;[else (error 'desugar "not implemented")]
    ))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Implémantation pour l'exo
;;;;;;;;;;;;;;;;;;
(define (recLamS [pars : (Listof Symbol)] [body : ExpS]) : Exp
  (cond
    [(empty? pars) (desugar body)]
    [else (lamE (first pars) (recLamS (rest pars) body))]
    ))

(define (recAppS [fun : Exp] [args : (Listof ExpS)]): Exp
  (cond
    ;Si il ne rest qu'un element. 
    [(empty? (rest args)) (appE fun (desugar (first args)))]
    [else (recAppS (appE fun (desugar (first args))) (rest args))]
    ))

(define (recNumS [n : Number]): ExpS
  (cond
    [(= n 0) (idS 'x)]
    [else (appS (idS 'f) (list (recNumS (- n 1))))]
    ))

(define (divInter [m : ExpS] [n : ExpS]) : ExpS
  (parse `{letrec {[divRec {lambda {m n k}
                        {if {zero? k} ;Doit etre la premiere verification.
                            {+ 1 {divRec m n n}}
                            {if {zero? m}
                                0
                                {divRec {- m 1} n {- k 1}}}}}]}
          {divRec m n n} }))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Substitution
(define (subst [what : Exp] [for : Symbol] [in : Exp]) : Exp
  (type-case Exp in
    [(idE s) (if (equal? s for) what in)]
    [(lamE par body) (if (equal? par for) in (lamE par (subst what for body)))]
    [(appE fun arg) (appE (subst what for fun) (subst what for arg))]))

; Interpréteur (pas de décente dans un lambda)
(define (interp [e : Exp]) : Exp
  (type-case Exp e
    [(appE fun arg)
     (type-case Exp (interp fun)
       [(lamE par body) (interp (subst (interp arg) par body))]
       [else e])]
    [else e]))

; Concaténation de chaînes de caractères contenues dans une liste
(define (strings-append [strings : (Listof String)]) : String
  (foldr string-append "" strings))

; Affichage lisible d'une lambda-expression
(define (expr->string [e : Exp]) : String
  (type-case Exp e
    [(idE s) (symbol->string s)]
    [(lamE par body) (strings-append (list "λ" (symbol->string par) "." (expr->string body)))]
    [(appE fun arg)
     (let ([fun-string (if (lamE? fun)
                           (strings-append (list "(" (expr->string fun) ")"))
                           (expr->string fun))]
           [arg-string (if (idE? arg)
                           (expr->string arg)
                           (strings-append (list "(" (expr->string arg) ")")))])
       (if (and (lamE? fun) (not (idE? arg)))
           (string-append fun-string arg-string)
           (strings-append (list fun-string " " arg-string))))]))

; Transforme une expression en nombre si possible
(define (expr->number [e : Exp]) : Number
  (type-case Exp (interp e)
    [(lamE f body-f)
     (type-case Exp (interp body-f)
       [(lamE x body-x)
        (destruct body-x f x)]
       [else (error 'expr->number "not a number")])]
    [else (error 'expr->number "not a number")]))
          
; Compte le nombre d'application de f à x
(define (destruct [e : Exp] [f : Symbol] [x : Symbol]) : Number
  (type-case Exp (interp e)
    [(idE s) (if (equal? s x)
                 0
                 (error 'expr->number "not a number"))]
    [(lamE par body) (error 'expr->number "not a number")]
    [(appE fun arg) (if (equal? fun (idE f))
                        (+ 1 (destruct arg f x))
                        (error 'expr->number "not a number"))]))

; Transforme une expression en booléen si possible
(define (expr->boolean [e : Exp]) : Boolean
  (type-case Exp (interp e)
    [(lamE x body-x)
     (type-case Exp (interp body-x)
       [(lamE y body-y)
        (type-case Exp (interp body-y)
          [(idE s) (cond
                     ((equal? x s) #t)
                     ((equal? y s) #f)
                     (else (error 'expr->boolean "not a boolean")))]
          [else (error 'expr->boolean "not a boolean")])]
       [else (error 'expr->boolean "not a boolean")])]
    [else (error 'expr->boolean "not a boolean")]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-number expr)
  (expr->number (desugar (parse expr))))

(define (interp-boolean expr)
  (expr->boolean (desugar (parse expr))))