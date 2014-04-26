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