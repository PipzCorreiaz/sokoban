(compile-file "heuristicas.lisp")
(load "heuristicas")

(defun 1-samp (problema profundidade-maxima)
  "Algoritmo de procura em profundidade primeiro."

  (let ((estado= (problema-estado= problema))
        (objectivo? (problema-objectivo? problema)))

    (labels ((esta-no-caminho? (estado caminho)
                               (member estado caminho :test estado=))

             (procura-prof (estado caminho prof-actual)
                           (cond ((funcall objectivo? estado) (list estado))
                                 ((= prof-actual profundidade-maxima) nil)
                                 ((esta-no-caminho? estado caminho) nil)
                                 (t
                                   ;; avancamos recursivamente, em profundidade,
                                   ;; para cada sucessor
                                   (let* ((sucs (problema-gera-sucessores problema estado))
                                          (sucs-number (list-length sucs))
                                          (suc nil)
                                          (solucao nil))
                                     (when (eql sucs-number 0)
                                       (return-from procura-prof nil))
                                     (setf suc (nth (random sucs-number) sucs))
                                     (setf solucao (procura-prof suc
                                                                 (cons estado caminho)
                                                                 (1+ prof-actual)))
                                     (when solucao
                                       (cons estado solucao)))))))

            (procura-prof (problema-estado-inicial problema) nil 0))))

(defun sondagem-iterativa (problema profundidade-maxima)
  (let ((solucao (1-samp problema profundidade-maxima)))
    (if solucao
        solucao
        (sondagem-iterativa problema profundidade-maxima))))

(defun ilds (problema profundidade-maxima)
  "Algoritmo de procura em profundidade primeiro."

  (let ((estado= (problema-estado= problema))
        (objectivo? (problema-objectivo? problema))
        (estados-gerados nil)
        (estados-gerados-importantes nil))

    (labels ((esta-no-caminho? (estado caminho)
                               (member estado caminho :test estado=))
             (procura-prof (estado caminho prof-actual iteracao)
                           (block procura-prof
                                  (cond ((funcall objectivo? (car estado)) (list (car estado)))
                                        ((= prof-actual profundidade-maxima) nil)
                                        ((esta-no-caminho? (car estado) caminho) nil)
                                        (t
                                          ;; avancamos recursivamente, em profundidade,
                                          ;; para cada sucessor
                                          (let* ((sucs (second estado))
                                                 (sucs-number (list-length sucs))
                                                 (suc nil)
                                                 (solucao nil))
                                            (when (eql sucs-number 0)
                                              (return-from procura-prof nil))
                                            (when (not (member estado estados-gerados-importantes :test #'equalp))
                                              (setf estados-gerados-importantes (append estados-gerados-importantes (list estado))))
                                            (setf suc (list (first sucs) (sucessores-ordernados (problema-gera-sucessores problema (first sucs)) (problema-heuristica problema))))
                                            (pop sucs)
                                            (setf (second estado) sucs)
                                            (setf estados-gerados-importantes (append estados-gerados-importantes (list suc)))
                                            (setf solucao (procura-prof suc
                                                                        (cons (car estado) caminho)
                                                                        (1+ prof-actual)
                                                                        iteracao))
                                            (when solucao
                                              (return-from procura-prof (cons (car estado) solucao))))))))
            (looper (estado caminho prof-atual iteracao)
                    (block blabla
                           (let ((resultado nil))
                             ; (format t "ITERACAO ~d~%" iteracao)
                             (when (and (= iteracao 0) (null estados-gerados))
                               ; (setf estados-gerados (list (cons estado iteracao))))
                               (setf estados-gerados (list (list estado (sucessores-ordernados (problema-gera-sucessores problema estado) (problema-heuristica problema))))))
                             (dolist (estado-gerado estados-gerados)
                               (setf resultado (procura-prof estado-gerado caminho prof-atual iteracao))
                               (when resultado
                                 (return-from blabla resultado)))
                             (setf estados-gerados estados-gerados-importantes)
                             ; (format t "ESTADOS-GERADOS: ~A~%~%~%" estados-gerados)
                             (setf estados-gerados-importantes nil)
                             (looper estado caminho prof-atual (1+ iteracao))))))
                             ;))))
            (looper (problema-estado-inicial problema) nil 0 0))))

(defun ida* (problema &key espaco-em-arvore?)
  (let ((estado= (problema-estado= problema))
        (heur (problema-heuristica problema))
        (fun-custo (problema-custo problema))
        (objectivo? (problema-objectivo? problema)))

    (labels ((esta-no-caminho? (estado caminho)
                               (unless espaco-em-arvore?
                                 (member estado caminho :test estado=)))

             (prof (estado custo-max custo-caminho caminho)
                   (block prof
                          (if (esta-no-caminho? estado caminho)
                              nil
                              (let ((custo (+ custo-caminho (funcall heur estado))))
                                (cond ((> custo custo-max) custo)
                                      ((funcall objectivo? estado) (list estado))
                                      (t
                                        (let ((min-custo most-positive-fixnum))
                                          (dolist (suc (problema-gera-sucessores
                                                         problema estado))
                                            (let ((solucao (prof suc
                                                                 custo-max
                                                                 (+ custo-caminho
                                                                    (funcall fun-custo suc))
                                                                 (or espaco-em-arvore?
                                                                     (cons estado
                                                                           caminho)))))
                                              (if (numberp solucao)
                                                  (setf min-custo (min min-custo
                                                                       solucao))
                                                  (if solucao
                                                      (return-from prof (cons estado
                                                                              solucao))))))
                                          min-custo))))))))

            (let ((custo-max 0))
              (loop
                (setf *todos-estados-gerados* (make-hash-table :test 'equal))
                (let ((solucao (prof (problema-estado-inicial problema)
                                     custo-max
                                     0
                                     nil)))
                  (if (numberp solucao)
                      (if (> solucao custo-max)
                          (setf custo-max solucao)
                          (return nil))
                      (return solucao))))))))

(defun procura (problema tipo-procura
        &key (profundidade-maxima most-positive-fixnum)
             (espaco-em-arvore? nil))
  "Dado um problema e um tipo de procura devolve uma lista com: a
  solucao para o problema (a lista de estados desde o estado inicial
  ate' ao estado final), ou nil caso nao encontre a solucao; tempo
  gasto na procura (em internal-time-units); numero de nos expandidos;
  numero de nos gerados."

  (flet ((faz-a-procura (problema tipo-procura
             profundidade-maxima espaco-em-arvore?)
       ;; Usamos cond em vez de case porque nao sabemos de que
       ;; package veem os simbolos (o string-equal funciona com o
       ;; symbol-name do simbolo e e' "case-insensitive")

       ;; Actualmente, apenas a procura em largura, o A* e o IDA*
       ;; estao a aproveitar a informacao do espaco de estados ser
       ;; uma arvore
       (cond ((string-equal tipo-procura "largura")
          (largura-primeiro problema
                    :espaco-em-arvore? espaco-em-arvore?))
         ((string-equal tipo-procura "profundidade")
          (profundidade-primeiro problema profundidade-maxima))
         ((string-equal tipo-procura "1-samp")
          (1-samp problema profundidade-maxima))
         ((string-equal tipo-procura "sondagem.iterativa")
          (sondagem-iterativa problema profundidade-maxima))
         ((string-equal tipo-procura "ilds")
          (ilds problema profundidade-maxima))
         ((string-equal tipo-procura "hill.climbing")
          (hill-climbing problema))
         ((string-equal tipo-procura "tempera")
          (tempera-simulada problema))
         ((string-equal tipo-procura "profundidade-iterativa")
          (profundidade-iterativa problema profundidade-maxima))
         ((string-equal tipo-procura "a*")
          (a* problema :espaco-em-arvore? espaco-em-arvore?))
         ((string-equal tipo-procura "ida*")
          (ida* problema :espaco-em-arvore? espaco-em-arvore?)))))

    (let ((*nos-gerados* 0)
      (*nos-expandidos* 0)
      (tempo-inicio (get-internal-run-time)))
      (let ((solucao (faz-a-procura problema tipo-procura
                    profundidade-maxima
                    espaco-em-arvore?)))
    (list solucao
          (- (get-internal-run-time) tempo-inicio)
          *nos-expandidos*
          *nos-gerados*)))))

(defun menor-heuristica (el1 el2)
  (< (cdr el1) (cdr el2)))

(defun sucessores-ordernados (sucessores heuristica)
  (let ((heuristicos nil)
        (suc nil))
    (dolist (sucessor sucessores)
      (setf suc (cons sucessor (funcall heuristica sucessor)))
      (push suc heuristicos))
    (sort heuristicos #'menor-heuristica)
    (mapcar 'car heuristicos)))

(defun sucessores-ordernados-heuristica (sucessores heuristica)
  (let ((heuristicos nil)
        (suc nil))
    (dolist (sucessor sucessores)
      (setf suc (cons sucessor (funcall heuristica sucessor)))
      (push suc heuristicos))
    (sort heuristicos #'menor-heuristica)))


(defun schedule (tempo)
  (- tempo 0.033))

(defun hill-climbing (problema)
  (let ((estado-atual (cons (problema-estado-inicial problema) most-positive-fixnum))
        (sucessores nil))
    (block cicle
           (loop
             (setf sucessores (sucessores-ordernados-heuristica (problema-gera-sucessores  problema (car estado-atual))
                                                                (problema-heuristica problema)))
             (if (null sucessores)
                 (return-from cicle estado-atual)
                 (if (< (cdr (first sucessores)) (cdr estado-atual))
                     (setf estado-atual (first sucessores))
                     (return-from cicle estado-atual)))))))

(defun tempera-simulada (problema)
  (let ((estado-atual (cons (problema-estado-inicial problema) most-positive-fixnum))
        (estado-seguinte nil)
        (sucessores nil)
        (intervalo 0)
        (tt 100)
        (e 2.71828))
    (block cicle
           (loop
             (setf tt (schedule tt))
             (setf sucessores (sucessores-ordernados-heuristica (problema-gera-sucessores  problema (car estado-atual))
                                                                (problema-heuristica problema)))
             (when (not (null sucessores))
               (setf estado-seguinte (nth (random (+ (- (list-length sucessores) 1) 1)) sucessores))
               (setf intervalo (- (cdr estado-atual) (cdr estado-seguinte)))
               (when (or (> intervalo 0) (< (expt e (/ intervalo tt)) (- 1 (random 2))))
                 (setf estado-atual estado-seguinte)))

             (when (null sucessores)
               (return-from cicle estado-atual))))))