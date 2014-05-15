;(in-package :user)

(defvar *mapa*)
(defvar *mapa-cantos*)
(defvar *todos-estados-gerados* (make-hash-table :test 'equal))
(defvar *posicoes-caixas-originais*)
(defvar *posicao-homem-original*)
(defvar *children*)
(defvar *parents*)


(defun h1 (estado)
  (let ((caixas (first estado))
        (destinos (copy-list (mapa-sokoban-destinos *mapa*)))
        (dist-min 1000)
        (index-min nil)
        (index 0)
        (res 0))
    (dolist (caixa caixas)
      (dolist (destino destinos)
        (let ((dist (+ (abs (- (first caixa)
                               (first destino)))
                       (abs (- (second caixa)
                               (second destino))))))
          (when (< dist dist-min)
            (setf dist-min dist)
            (setf index-min index))
          (setf index (1+ index))))
      (setf res (+ res dist-min))
      (setf destinos (remove-nth destinos index-min))
      (setf dist-min 1000)
      (setf index-min nil)
      (setf index 0))
    res))


(defun h2 (estado)
  (let* ((caixas (first estado))
         (mapa (mapa-sokoban-mapa *mapa*))
         (ocupadas (coloca-caixotes (mapa-sokoban-mapa-aux *mapa*) caixas))
         (num-caixas (list-length caixas))
         (destinos (mapa-sokoban-destinos *mapa*))
         (res 0))
    (dolist (caixa caixas)
      (if (destino? destinos (first caixa) (second caixa))
          (setf num-caixas (1- num-caixas))
          (setf res (+ res (list-length (jogadas-validas2 mapa ocupadas (first caixa) (second caixa)))))))
    (- (* 4 num-caixas) res)))



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


(defun dds (problema profundidade-maxima)
  "Algoritmo de procura em profundidade primeiro."

  (let ((estado= (problema-estado= problema))
        (objectivo? (problema-objectivo? problema))
        (estados-gerados (make-hash-table))
        (lista-aux nil))

    (labels ((esta-no-caminho? (estado caminho)
                               (member estado caminho :test estado=))
             (procura-prof (estado caminho prof-actual)
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
                                            (setf suc (list (first sucs) (sucessores-ordernados (problema-gera-sucessores problema (first sucs)) (problema-heuristica problema))))
                                            (pop sucs)
                                            (setf (second estado) sucs)
                                            (when (> (list-length (second suc)) 0)
                                              (setf (gethash (1+ prof-actual) estados-gerados) (append (gethash (1+ prof-actual) estados-gerados) (list suc))))
                                            (setf solucao (procura-prof suc
                                                                        (cons (car estado) caminho)
                                                                        (1+ prof-actual)))
                                            (when solucao
                                              (return-from procura-prof (cons (car estado) solucao))))))))
            (looper (estado caminho prof-atual)
                    (block blabla
                           (let ((resultado nil)
                                 (prox-prof (1+ prof-atual)))
                             (when (= prof-atual 0)
                               (setf (gethash prox-prof estados-gerados) (list (list estado (sucessores-ordernados (problema-gera-sucessores problema estado) (problema-heuristica problema))))))
                             (block main-loop
                                    (loop
                                      (when (null (gethash prox-prof estados-gerados))
                                            (return-from main-loop nil))
                                      (dolist (estado-gerado (gethash prox-prof estados-gerados))
                                        (setf resultado (procura-prof estado-gerado caminho prox-prof))
                                        (when resultado
                                          (return-from blabla resultado))
                                        (when (second estado-gerado)
                                          (push estado-gerado lista-aux)))
                                       (setf (gethash prox-prof estados-gerados) lista-aux)
                                       (setf lista-aux nil)))
                             (looper estado caminho prox-prof)))))
            (looper (problema-estado-inicial problema) nil 0))))



(defun ida*-g004 (problema &key espaco-em-arvore?)
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

(defun procura-g004 (problema tipo-procura
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
         ((string-equal tipo-procura "dds")
          (dds problema profundidade-maxima))
         ((string-equal tipo-procura "hill.climbing")
          (hill-climbing problema))
         ((string-equal tipo-procura "tempera")
          (tempera-simulada problema))
         ((string-equal tipo-procura "profundidade-iterativa")
          (profundidade-iterativa problema profundidade-maxima))
         ((string-equal tipo-procura "a*")
          (a* problema :espaco-em-arvore? espaco-em-arvore?))
         ((string-equal tipo-procura "ida*")
          (ida*-g004 problema :espaco-em-arvore? espaco-em-arvore?)))))

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
      (setf heuristicos (inserir-ordenado suc heuristicos)))
    (mapcar 'car heuristicos)))

(defun sucessores-ordernados-heuristica (sucessores heuristica)
  (let ((heuristicos nil)
        (suc nil))
    (dolist (sucessor sucessores)
      (setf suc (cons sucessor (funcall heuristica sucessor)))
      (setf heuristicos (inserir-ordenado suc heuristicos)))))


(defun schedule (tempo)
  (- tempo 0.033))



(defun inserir-ordenado (elemento lista)
  (cond ((null lista)
         (list elemento))
        ((>= (cdr (car lista)) (cdr elemento))
         (cons elemento (cons (car lista) (cdr lista))))
        ((< (cdr (car lista)) (cdr elemento))
         (cons (car lista) (inserir-ordenado elemento (cdr lista))))))


(defun quicksort (l)
  "Quicksort divides all elements into smaller or larger than the first element.
  These are then sorted recursivly with the first element in the middle"
  (if (null l) nil                      ; Recursive case
      (labels ((bigger-el (x) (or (and (not (< (first x) (first (first l)))) (> (first x) (first (first l)))) (> (second x) (second (first l)))))) ; t if x > first
              (let ((smaller (remove-if #'bigger-el (rest l))) ; all < first
                    (bigger  (remove-if-not #'bigger-el (rest l)))) ; all > first
                (append (quicksort smaller) (list (first l)) (quicksort bigger))))))

(defun passos (caminho)
	(reverse (second (first (last caminho)))))


(defun objectivo (estado)
  (let* ((mapa *mapa*)
         (caixotes (first estado))
         (homem (first (second estado)))
         (posicoes-certas 0))
    (when (ha-caminho *mapa* *posicoes-caixas-originais* (first *posicao-homem-original*) (second *posicao-homem-original*)
                      (first homem) (second homem))
      (dotimes (i (length caixotes))
        (dolist (p caixotes)
          (when (equal p (nth i (mapa-sokoban-destinos mapa)))
            (incf posicoes-certas))))
      (= posicoes-certas (length caixotes)))))

(defun copy-estado (estado)
	(let ((caixas (copy-list (first estado)))
			(pos (copy-list (second estado))))
		(list caixas pos)))


(defun jogadas-validas3 (mapa ocupadas x y)
  (let ((res nil))
    (unless (or (aref mapa (1+ x) y) (aref ocupadas (1+ x) y) (aref mapa (1- x) y) (aref ocupadas (1- x) y))
    	(push (list (1+ x) y) res)
    	(push (list (1- x) y) res))
    (unless (or (aref mapa x (1+ y)) (aref ocupadas x (1+ y)) (aref mapa x (1- y)) (aref ocupadas x (1- y)))
    	(push (list x (1+ y)) res)
    	(push (list x (1- y)) res))
    res))

(defun destino? (destinos x y)
  	(member (list x y) destinos :test #'equalp))

(defun vertical-freeze-deadlock? (x y ocupadas)
  (let ((res nil))
    (when (destino? (mapa-sokoban-destinos *mapa*) x y)
      (return-from vertical-freeze-deadlock? nil))
    (setf res (or (casa-ocupada *mapa* (1+ x) y)
                  (casa-ocupada *mapa* (1- x) y)
                  (and (corner-deadlock? (list (1+ x) y))
                       (corner-deadlock? (list (1- x) y)))))
    (when (not res)
      (when (casa-preenchida ocupadas (1+ x) y)
        (setf res (horizontal-freeze-deadlock? (1+ x) y ocupadas)))
      (when (casa-preenchida ocupadas (1- x) y)
        (setf res (horizontal-freeze-deadlock? (1- x) y ocupadas))))
    res))

(defun horizontal-freeze-deadlock? (x y ocupadas)
  (let ((res nil))
    (when (destino? (mapa-sokoban-destinos *mapa*) x y)
      (return-from horizontal-freeze-deadlock? nil))
    (setf res (or (casa-ocupada *mapa* x (1+ y))
                  (casa-ocupada *mapa* x (1- y))
                  (and (corner-deadlock? (list x (1+ y)))
                       (corner-deadlock? (list x (1- y))))))
    (when (not res)
      (when (casa-preenchida ocupadas x (1+ y))
        (setf res (vertical-freeze-deadlock? x (1+ y) ocupadas)))
      (when (casa-preenchida ocupadas x (1- y))
        (setf res (vertical-freeze-deadlock? x (1- y) ocupadas))))
    res))

(defun freeze-deadlock? (posicao-atual proxima-posicao ocupadas)
  (let ((x (first proxima-posicao))
        (y (second proxima-posicao))
        (copia-ocupadas (copy-array ocupadas)))
    (setf (aref copia-ocupadas (first posicao-atual) (second posicao-atual)) nil)
    (and (horizontal-freeze-deadlock? x y copia-ocupadas)
         (vertical-freeze-deadlock? x y copia-ocupadas))))

(defun corner-deadlock? (posicao)
  (eql (casa-preenchida *mapa-cantos* (first posicao) (second posicao)) 'DL))


(defun tunnel (mapa caixa homem)
  (let* ((i 1)
         (diff-l (- (car caixa) (car homem)))
         (diff-c (- (cadr caixa) (cadr homem)))
         (parede1 nil)
         (parede2 nil)
         (caminho nil)
         (destinos (mapa-sokoban-destinos *mapa*)))
    (if (eq (cadr caixa) (cadr homem))
        (loop
          (let ((next-pos (+ (car caixa) (* i diff-l))))
            (setf parede1 (1- (cadr caixa)))
            (setf parede2 (1+ (cadr caixa)))
            (push (list (+ (car homem) (* i diff-l)) (cadr homem)) caminho)
            (when (or (destino? destinos next-pos (cadr caixa))
                      (aref mapa (+ (car caixa) (* (1+ i) diff-l)) (cadr caixa))
                      (not (and (aref mapa next-pos parede1) (aref mapa next-pos parede2))))
              (return-from tunnel (list (list next-pos (cadr caixa)) caminho)))
            (setf i (1+ i))))
        (loop
          (let ((next-pos (+ (cadr caixa) (* i diff-c))))
            (setf parede1 (1- (car caixa)))
            (setf parede2 (1+ (car caixa)))
            (when (or (destino? destinos next-pos (cadr caixa))
                      (aref mapa (car caixa) (+ (cadr caixa) (* (1+ i) diff-c)))
                      (not (and (aref mapa parede1 next-pos) (aref mapa parede2 next-pos))))
              (return-from tunnel (list (list (car caixa) next-pos) caminho)))
            (setf i (1+ i)))))))

(defun player-surrounded? (caixas proxima-posicao)
  (let ((ocupadas (coloca-caixotes (limpa-mapa-aux *mapa*) caixas)))
    (null (jogadas-validas2 (mapa-sokoban-mapa *mapa*) ocupadas (first proxima-posicao) (second proxima-posicao)))))


(defun operador (estado)
  (let* ((mapa *mapa*)
         (novo-estado nil)
         (proxima-posicao nil)
         (sucessores nil)
         (homem (first (second estado))))
    (dotimes (i (length (first estado)))
      (let ((caixa (nth i (first estado)))
            (caminho nil)
            (ocupadas (coloca-caixotes (limpa-mapa-aux mapa) (first estado))))
        (dolist (jogada (jogadas-validas3 (mapa-sokoban-mapa mapa) ocupadas (first caixa) (second caixa)))
          (when (ha-caminho mapa (first estado) (first homem) (second homem) (first jogada) (second jogada))
            (setf novo-estado (copy-estado estado))
            (let ((tunnel-res (tunnel (mapa-sokoban-mapa mapa) caixa jogada)))
              (setf proxima-posicao (first tunnel-res))
              (setf ocupadas (coloca-caixotes (limpa-mapa-aux mapa) (first estado)))
              (when (and (not (corner-deadlock? proxima-posicao)) (not (freeze-deadlock? caixa proxima-posicao ocupadas)))
                (setf (nth i (first novo-estado)) proxima-posicao)
                (when (not (gethash (list (first novo-estado) caixa) *todos-estados-gerados*))
                  (setf caminho (encontra-caminho mapa (first estado) (first homem) (second homem) (first jogada) (second jogada)))
                  (setf caminho (reverse caminho))
                  (setf caminho (nconc (second tunnel-res) caminho))
                  ;(push caixa caminho)
                  (setf (second novo-estado) (nconc caminho (cdr (second novo-estado))))
                  (setf (gethash (list (first novo-estado) caixa) *todos-estados-gerados*) t)
                  (setf sucessores (cons novo-estado sucessores)))))))))
    sucessores))

(defun list< (a b)
  (cond ((null a) (not (null b)))
        ((null b) nil)
        ((= (first a) (first b)) (list< (rest a) (rest b)))
        (t (< (first a) (first b)))))

(defun jogadas-muito-validas (caixas caixa)
  (let* ((mapa-com-caixas (coloca-caixotes (copy-array (mapa-sokoban-mapa *mapa*)) caixas))
         (n-linhas (mapa-sokoban-nlinhas *mapa*))
         (n-colunas (mapa-sokoban-ncolunas *mapa*))
         (jv (jogadas-validas2 (mapa-sokoban-mapa *mapa*) mapa-com-caixas (first caixa) (second caixa)))
         (res nil))
    (dolist (jogada jv)
      (let ((i 1)
            (diff-l (- (car jogada) (car caixa)))
            (diff-c (- (cadr jogada) (cadr caixa)))
            (caminho nil))
        (if (= diff-l 0)
            (block loopjogadal
                   (loop
                     (let ((coluna (+ (cadr caixa) (* i diff-c)))
                           (coluna-homem (+ (cadr caixa) (* (1+ i) diff-c))))
                       (when (or (> coluna-homem (- n-colunas 2))
                                 (< coluna-homem 1)
                                 (aref mapa-com-caixas (car caixa) coluna)
                                 (aref mapa-com-caixas (car caixa) coluna-homem))
                         (return-from loopjogadal))
                       (setf caminho (cons (list (car caixa) coluna) caminho))
                       (setf res (cons (list jogada
                                             (list (car caixa) coluna)
                                             (cons (list (car caixa) coluna-homem) caminho))
                                       res))
                       (setf i (1+ i)))))
            (block loopjogadac
                   (loop
                     (let ((linha (+ (car caixa) (* i diff-l)))
                           (linha-homem (+ (car caixa) (* (1+ i) diff-l))))
                       (when (or (> linha-homem (- n-linhas 2))
                                 (< linha-homem 1)
                                 (aref mapa-com-caixas linha (cadr caixa))
                                 (aref mapa-com-caixas linha-homem (cadr caixa)))
                         (return-from loopjogadac))
                       (setf caminho (cons (list linha (cadr caixa)) caminho))
                       (setf res (cons (list jogada
                                             (list linha (cadr caixa))
                                             (cons (list linha-homem (cadr caixa)) caminho))
                                       res))
                       (setf i (1+ i))))))))
    res))

(defun reversed-operator (estado)
  (let ((novo-estado nil)
        (sucessores nil)
        (homem (first (second estado)))
        (filhos 0))
    (dotimes (i (length (first estado)))
      (let ((caixa (nth i (first estado))))
        (dolist (jogada-caminho (jogadas-muito-validas (first estado) caixa))
          (let* ((jogada (first jogada-caminho))
                 (proxima-posicao-caixa (second jogada-caminho))
                 (caminho nil)
                 (proxima-posicao-homem (car (third jogada-caminho))))
            (setf novo-estado (copy-estado estado))
            (setf (nth i (first novo-estado)) proxima-posicao-caixa)
            (if (= (list-length (second estado)) 1)
                (setf caminho (list (list 999 999)))
                (setf caminho (encontra-caminho *mapa* (first estado) (first jogada) (second jogada) (first homem) (second homem))))
            (unless (or (null caminho)
                        (gethash (sxhash (list (first novo-estado) proxima-posicao-homem)) *todos-estados-gerados*)
                        (player-surrounded? (first novo-estado) proxima-posicao-homem))
              (incf filhos)
              (setf caminho (nconc (copy-list (third jogada-caminho)) (cdr caminho)))
              (setf (second novo-estado) (nconc caminho (cdr (second novo-estado))))
              (setf (gethash (sxhash (list (first novo-estado) proxima-posicao-homem)) *todos-estados-gerados*) t)
              (setf sucessores (cons novo-estado sucessores)))))))
    (unless (= filhos 0)
      (setf *children* (+ *children* filhos))
      (setf *parents* (1+ *parents*)))
      sucessores))

(defun compara-estado (estado1 estado2)
  (equalp estado1 estado2))

(defun compara-posicoes-caixas (estado1 estado2)
  (equalp (car estado1) (car estado2)))


(defun casa-preenchida (mapa i j)
  (aref mapa i j))


(defun elimina-cantos (mapa)
  (let ((linhas (mapa-sokoban-nlinhas *mapa*))
        (colunas (mapa-sokoban-ncolunas *mapa*))
        (destinos (mapa-sokoban-destinos *mapa*))
        (novo-mapa (copy-array mapa)))
    (dotimes (i linhas novo-mapa)
      (dotimes (j colunas)
        (when (and (> i 0) (> j 0) (< j (- colunas 1)) (< i (- linhas 1)))
          (when (and (or (and (casa-preenchida mapa (1+ i) j) (casa-preenchida mapa i (1+ j)))
                         (and (casa-preenchida mapa (1- i) j) (casa-preenchida mapa i (1+ j)))
                         (and (casa-preenchida mapa (1+ i) j) (casa-preenchida mapa i (1- j)))
                         (and (casa-preenchida mapa (1- i) j) (casa-preenchida mapa i (1- j))))
                     (not (casa-preenchida mapa i j))
                     (not (destino? destinos i j)))
            (setf (aref novo-mapa i j) 'DL)))))))


(defun novos-passos (caminho caixas homem)
  (let ((novo-caminho nil)
        (destino nil)
        (caminho-encontrado nil))
    (setf novo-caminho (second (first (last caminho))))
    (setf destino (first novo-caminho))
    (unless (null destino)
      (setf caminho-encontrado (encontra-caminho *mapa* caixas (first homem) (second homem) (first destino) (second destino)))
      (nconc caminho-encontrado (cdr novo-caminho)))
    caminho-encontrado))


(defun resolve-sokoban (filename tipo-procura)
  (let* ((estado-inicial (parse-ficheiro filename))
         (problema nil)
         (destinos nil)
         (caixas nil)
         (homem nil)
         (caminho nil)
         (procura nil)
         (resultado nil))
    (setf *parents* 0.0)
    (setf *children* 0.0)
    (setf *todos-estados-gerados* (make-hash-table :test 'equal))
    (setf *mapa* (first estado-inicial))
    (setf destinos (copy-list (mapa-sokoban-destinos *mapa*)))
    (setf caixas (copy-list (second estado-inicial)))
    (setf homem (copy-list (third estado-inicial)))
    (setf *posicoes-caixas-originais* caixas)
    (setf *posicao-homem-original* homem)
    (setf (mapa-sokoban-destinos *mapa*) caixas)
    (setf (second estado-inicial) destinos)
    ;(setf (third estado-inicial) nil)
    (setf *mapa-cantos* (elimina-cantos (mapa-sokoban-mapa *mapa*)))
    (setf estado-inicial (cdr estado-inicial))
    (setf (second estado-inicial) (list (second estado-inicial)))
    (setf problema (cria-problema estado-inicial
                                  ;(list #'operador)
                                  (list #'reversed-operator)
                                  :objectivo? #'objectivo
                                  :heuristica #'h2))
                                  ;:estado= #'compara-estado))
    (setf procura (procura-g004 problema tipo-procura))
    (setf caminho (first procura))
    ;(passos caminho)))
    (setf resultado (novos-passos caminho caixas homem))
    (format t "============================
  NÓS EXPANDIDOS: ~A
  NÓS GERADOS: ~A
  PROFUNDIDADE ATINGIDA: ~A
  CUSTO: ~A
  FACT. MÉD. RAMIFIC.: ~A
============================~%"
               (third procura)
               (fourth procura)
               (list-length (first procura))
               (list-length resultado)
               (if (= *parents* 0)
                   666999
                   (/ *children* *parents*)))
    resultado))


(defun remove-nth (lst index)
  (if (= index 0)
      (cdr lst)
      (cons (car lst) (remove-nth (cdr lst) (1- index)))))

