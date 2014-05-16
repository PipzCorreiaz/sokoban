(in-package :user)

(defvar *mapa-normal*)
(defvar *mapa-reversed*)
(defvar *mapa-cantos*)
(defvar *estados-gerados-normal* (make-hash-table :test 'equal))
(defvar *estados-gerados-reversed* (make-hash-table :test 'equal))
(defvar *gerados-reversed*)
(defvar *bidirectional-match*)
(defvar *posicoes-caixas-originais*)
(defvar *posicao-homem-original*)
(defvar *children*)
(defvar *parents*)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;            HEURISTICAS             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun h1-normal (estado)
  (let ((caixas (first estado))
        (destinos (copy-list (mapa-sokoban-destinos *mapa-normal*)))
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


(defun h1-reversed (estado)
  (let ((caixas (first estado))
        (destinos (copy-list (mapa-sokoban-destinos *mapa-reversed*)))
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


;conta as adjacentes das caixas que nao estao ja no destino
(defun h2-normal (estado)
  (let* ((caixas (first estado))
         (mapa (mapa-sokoban-mapa *mapa-normal*))
         (ocupadas (coloca-caixotes (mapa-sokoban-mapa-aux *mapa-normal*) caixas))
         (num-caixas (list-length caixas))
         (destinos (mapa-sokoban-destinos *mapa-normal*))
         (res 0))
    (dolist (caixa caixas)
      (if (destino? destinos (first caixa) (second caixa))
          (setf num-caixas (1- num-caixas))
          (setf res (+ res (list-length (jogadas-validas2 mapa ocupadas (first caixa) (second caixa)))))))
    (- (* 4 num-caixas) res)))

(defun h2-reversed (estado)
  (let* ((caixas (first estado))
         (mapa (mapa-sokoban-mapa *mapa-reversed*))
         (ocupadas (coloca-caixotes (mapa-sokoban-mapa-aux *mapa-reversed*) caixas))
         (num-caixas (list-length caixas))
         (destinos (mapa-sokoban-destinos *mapa-reversed*))
         (res 0))
    (dolist (caixa caixas)
      (if (destino? destinos (first caixa) (second caixa))
          (setf num-caixas (1- num-caixas))
          (setf res (+ res (list-length (jogadas-validas2 mapa ocupadas (first caixa) (second caixa)))))))
    (- (* 4 num-caixas) res)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;              PROCURAS              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



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
  (setf *estados-gerados-reversed* (make-hash-table :test 'equal))
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
                              (when (and (= iteracao 0) (null estados-gerados))
                                (setf estados-gerados (list (list estado (sucessores-ordernados (problema-gera-sucessores problema estado) (problema-heuristica problema))))))
                              (dolist (estado-gerado estados-gerados)
                                (setf resultado (procura-prof estado-gerado caminho prof-atual iteracao))
                                (when resultado
                                  (return-from blabla resultado)))
                              (setf estados-gerados estados-gerados-importantes)
                              (setf estados-gerados-importantes nil)
                              (looper estado caminho prof-atual (1+ iteracao))))))
            (looper (problema-estado-inicial problema) nil 0 0))))


(defun birectional-matcht? (gerados-reversed estado)
  (dolist (r gerados-reversed)
    (let ((homem1 (first (second r)))
          (homem2 (first (second estado))))
      (when (and (equal (first r) (first estado))
                 (ha-caminho *mapa-reversed* (first r) (first homem1) (second homem1) (first homem2) (second homem2)))
        (return-from birectional-matcht? r)))))
    


(defun bidirectional (problema-normal problema-reversed)
  (let ((estados-normal (list (problema-estado-inicial problema-normal)))
        (estados-reversed (list (problema-estado-inicial problema-reversed))))
    (loop
      (if (or (null estados-normal) (null estados-reversed))
          (return-from bidirectional nil)
          (progn
            (when (not (null estados-normal))
              (let ((estado (first estados-normal))
                    (objectivo? (problema-objectivo? problema-normal)))
                (when (funcall objectivo? estado)
                  (return-from bidirectional (list estado nil)))
                (pop estados-normal)
                (setf estados-normal (sucessores-ordernados (append (problema-gera-sucessores problema-normal estado)
                                                                    estados-normal)
                                                            (problema-heuristica problema-normal)))
                (when *bidirectional-match*
                  (return-from bidirectional *bidirectional-match*))))
            
            (when (not (null estados-reversed))
              (let ((estado (first estados-reversed))
                    (objectivo? (problema-objectivo? problema-reversed)))
                (when (funcall objectivo? estado)
                  (return-from bidirectional (list estado nil)))
                (pop estados-reversed)
                (setf estados-reversed (sucessores-ordernados (append (problema-gera-sucessores problema-reversed estado)
                                                                      estados-reversed)
                                                              (problema-heuristica problema-reversed))))))))))


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
                (setf *estados-gerados-reversed* (make-hash-table :test 'equal))
                (let ((solucao (prof (problema-estado-inicial problema)
                                     custo-max
                                     0
                                     nil)))
                  (if (numberp solucao)
                      (if (> solucao custo-max)
                          (setf custo-max solucao)
                          (return nil))
                      (return solucao))))))))


(defun menor-heuristica (el1 el2)
  (< (cdr el1) (cdr el2)))

(defun inserir-ordenado (elemento lista)
  (cond ((null lista)
         (list elemento))
        ((>= (cdr (car lista)) (cdr elemento))
         (cons elemento (cons (car lista) (cdr lista))))
        ((< (cdr (car lista)) (cdr elemento))
         (cons (car lista) (inserir-ordenado elemento (cdr lista))))))

(defun sucessores-ordernados (sucessores heuristica)
  (let ((heuristicos nil)
        (suc nil))
    (dolist (sucessor sucessores)
      (setf suc (cons sucessor (funcall heuristica sucessor)))
      (setf heuristicos (inserir-ordenado suc heuristicos)))
    ;(push suc heuristicos))
    ;(stable-sort heuristicos #'menor-heuristica)
    (mapcar 'car heuristicos)))

(defun sucessores-ordernados-heuristica (sucessores heuristica)
  (let ((heuristicos nil)
        (suc nil))
    (dolist (sucessor sucessores)
      (setf suc (cons sucessor (funcall heuristica sucessor)))
      (setf heuristicos (inserir-ordenado suc heuristicos)))))
;(push suc heuristicos))
;(stable-sort heuristicos #'menor-heuristica)))


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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;             PRINCIPAL              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ordena-lista (lista)
  (let ((nova-lista nil))
    (dolist (el lista nova-lista)
      (setf nova-lista (inserir-ordenado-2 el nova-lista)))))

(defun inserir-ordenado-2 (elemento lista)
  (cond ((null lista)
         (list elemento))
        ((> (first (car lista)) (first elemento))
         (cons elemento (cons (car lista) (cdr lista))))
        ((< (first (car lista)) (first elemento))
         (cons (car lista) (inserir-ordenado-2 elemento (cdr lista))))
        ((>= (second (car lista)) (second elemento))
         (cons elemento (cons (car lista) (cdr lista))))
        ((< (second (car lista)) (second elemento))
         (cons (car lista) (inserir-ordenado-2 elemento (cdr lista))))))

(defun remove-nth (lst index)
  (if (= index 0)
      (cdr lst)
      (cons (car lst) (remove-nth (cdr lst) (1- index)))))

(defun faz-caminho-normal (caminho)
  (reverse (second (first (last caminho)))))


(defun faz-caminho-reversed (caminho caixas homem)
  (let ((novo-caminho nil)
        (destino nil)
        (caminho-encontrado nil))
    (setf novo-caminho (second (first (last caminho))))
    (setf destino (first novo-caminho))
    (unless (null destino)
      (setf caminho-encontrado (encontra-caminho *mapa-reversed* caixas (first homem) (second homem) (first destino) (second destino)))
      (nconc caminho-encontrado (cdr novo-caminho)))
    caminho-encontrado))


(defun faz-caminho-bidirectional (estados)
  (cond ((and (null (first estados)) (null (second estados)))
         nil)
        ((null (first estados))
         (second estados))
        ((null (second estados))
         (reverse (second (first estados))))
        (t (let ((estado-normal (first estados))
                 (estado-reversed (second estados))
                 (res nil)
                 (homem1 nil)
                 (homem2 nil))
             (setf homem1 (first (second estado-normal)))
             (setf homem2 (first (second estado-reversed)))
             (unless (null (cdr (second estado-reversed)))
               (setf res (append (cdr (encontra-caminho *mapa-reversed* (first estado-normal)
                                                        (first homem1) (second homem1)
                                                        (first homem2) (second homem2)))
                                 (cdr (second estado-reversed)))))
             (setf res (append (reverse (second estado-normal)) res))
             res))))


(defun objectivo (estado)
  (let* ((mapa *mapa-normal*)
         (caixotes (first estado))
         (posicoes-certas 0))
    (dotimes (i (list-length caixotes))
      (dolist (p caixotes)
        (when (equal p (nth i (mapa-sokoban-destinos mapa)))
          (incf posicoes-certas))))
    (= posicoes-certas (list-length caixotes))))



(defun objectivo-reversed (estado)
  (let* ((mapa *mapa-reversed*)
         (caixotes (first estado))
         (homem (first (second estado)))
         (posicoes-certas 0))
    (dotimes (i (list-length caixotes))
      (dolist (p caixotes)
        (when (and (equal p (nth i (mapa-sokoban-destinos mapa)))
                   (ha-caminho *mapa-reversed* *posicoes-caixas-originais* (first *posicao-homem-original*) (second *posicao-homem-original*)
                               (first homem) (second homem)))
          (incf posicoes-certas))))
    (= posicoes-certas (list-length caixotes))))


(defun copy-structure-sokoban (mapa)
  (let ((copy (make-mapa-sokoban)))
    (setf (mapa-sokoban-mapa copy) (copy-array (mapa-sokoban-mapa mapa)))
    (setf (mapa-sokoban-destinos copy) (copy-list (mapa-sokoban-destinos mapa)))
    (setf (mapa-sokoban-mapa-aux copy) (copy-array (mapa-sokoban-mapa-aux mapa)))
    (setf (mapa-sokoban-nlinhas copy) (mapa-sokoban-nlinhas mapa))
    (setf (mapa-sokoban-ncolunas copy) (mapa-sokoban-ncolunas mapa))
    copy))


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
    (when (destino? (mapa-sokoban-destinos *mapa-normal*) x y)
      (return-from vertical-freeze-deadlock? nil))
    (setf res (or (casa-ocupada *mapa-normal* (1+ x) y)
                  (casa-ocupada *mapa-normal* (1- x) y)
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
    (when (destino? (mapa-sokoban-destinos *mapa-normal*) x y)
      (return-from horizontal-freeze-deadlock? nil))
    (setf res (or (casa-ocupada *mapa-normal* x (1+ y))
                  (casa-ocupada *mapa-normal* x (1- y))
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
         (destinos (mapa-sokoban-destinos *mapa-normal*)))
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
            (push (list (car homem) (+ (cadr homem) (* i diff-c))) caminho)
            (when (or (destino? destinos next-pos (cadr caixa))
                      (aref mapa (car caixa) (+ (cadr caixa) (* (1+ i) diff-c)))
                      (not (and (aref mapa parede1 next-pos) (aref mapa parede2 next-pos))))
              (return-from tunnel (list (list (car caixa) next-pos) caminho)))
            (setf i (1+ i)))))))

(defun tunnel-2 (caixas caixa homem)
  (let* ((i 1)
         (diff-l (- (car homem) (car caixa)))
         (diff-c (- (cadr homem) (cadr caixa)))
         (parede1 nil)
         (parede2 nil)
         (caminho (list homem))
         (proxima-posicao-homem nil)
         (ocupadas (coloca-caixotes (limpa-mapa-aux *mapa-reversed*) caixas))
         (destinos (mapa-sokoban-destinos *mapa-reversed*)))
    (if (eq (cadr caixa) (cadr homem))
        (loop
          (let ((next-x (+ (car caixa) (* i diff-l)))
                (next-x-homem (+ (car homem) (* i diff-l))))
            (setf parede1 (list next-x (1+ (cadr caixa))))
            (setf parede2 (list next-x (1- (cadr caixa))))
            (setf proxima-posicao-homem (list next-x-homem (cadr homem)))
            (when (or (casa-ocupada *mapa-reversed* (first proxima-posicao-homem) (second proxima-posicao-homem))
                      (casa-preenchida ocupadas (first proxima-posicao-homem) (second proxima-posicao-homem)))
              (return-from tunnel-2 nil))
            (when (or (casa-ocupada *mapa-reversed* (+ (first proxima-posicao-homem) diff-l) (second proxima-posicao-homem))
                      (casa-preenchida ocupadas (+ (first proxima-posicao-homem) diff-l) (second proxima-posicao-homem)))
              (return-from tunnel-2 (list (list next-x (cadr caixa)) proxima-posicao-homem caminho)))
            (when (or (destino? destinos next-x (cadr caixa))
                      (not (casa-ocupada *mapa-reversed* (first parede1) (second parede1)))
                      (not (casa-ocupada *mapa-reversed* (first parede2) (second parede2))))
              (return-from tunnel-2 (list (list next-x (cadr caixa)) proxima-posicao-homem caminho)))
            (push proxima-posicao-homem caminho)
            (incf i)))
        (loop
          (let ((next-y (+ (* i diff-c) (cadr caixa)))
                (next-y-homem (+ (* i diff-c) (cadr homem))))
            (setf parede1 (list (1+ (car caixa)) next-y))
            (setf parede2 (list (1- (car caixa)) next-y))
            (setf proxima-posicao-homem (list (car homem) next-y-homem))
            (when (casa-ocupada *mapa-reversed* (first proxima-posicao-homem) (second proxima-posicao-homem))
              (return-from tunnel-2 nil))
            (when (or (casa-ocupada *mapa-reversed* (first proxima-posicao-homem) (+ (second proxima-posicao-homem) diff-c))
                      (casa-preenchida ocupadas (first proxima-posicao-homem)  (+ (second proxima-posicao-homem) diff-c)))
              (return-from tunnel-2 (list (list (car caixa) next-y) proxima-posicao-homem caminho)))
            (when (or (destino? destinos (car caixa) next-y)
                      (not (casa-ocupada *mapa-reversed* (first parede1) (second parede1)))
                      (not (casa-ocupada *mapa-reversed* (first parede2) (second parede2))))
              (return-from tunnel-2 (list (list (car caixa) next-y) proxima-posicao-homem caminho)))
            (push proxima-posicao-homem caminho)
            (incf i))))))

(defun player-surrounded? (caixas proxima-posicao)
  (let ((ocupadas (coloca-caixotes (limpa-mapa-aux *mapa-reversed*) caixas)))
    (null (jogadas-validas2 (mapa-sokoban-mapa *mapa-reversed*) ocupadas (first proxima-posicao) (second proxima-posicao)))))


(defun operador (estado)
  (let* ((mapa *mapa-normal*)
         (novo-estado nil)
         (proxima-posicao nil)
         (sucessores nil)
         (homem (first (second estado)))
         (aux nil))
    (dotimes (i (list-length (first estado)))
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
                  (setf caminho (encontra-caminho mapa (first estado) (first homem) (second homem) (first jogada) (second jogada)))
                  (setf caminho (reverse caminho))
                  (setf caminho (nconc (second tunnel-res) caminho))
                  (setf (second novo-estado) (nconc caminho (cdr (second novo-estado))))
                  (let ((match (birectional-matcht? *gerados-reversed* novo-estado)))
                    (when match
                      (setf *bidirectional-match* (list novo-estado match))
                      (return-from operador nil)))
                  (setf aux (cons jogada aux))
                  (setf sucessores (cons novo-estado sucessores))))))));)
    (unless (null aux)
      (let* ((estado-jogadas-ordenados (list (ordena-lista (first estado)) (ordena-lista aux)))
             (hash-value (gethash (sxhash estado-jogadas-ordenados) *estados-gerados-normal*)))
        (when (null hash-value)
          (setf (gethash (sxhash estado-jogadas-ordenados) *estados-gerados-normal*) t)
          sucessores)))))


(defun reversed-operator (estado)
  (let ((novo-estado nil)
        (sucessores nil)
        (homem (first (second estado)))
        (pos-diff nil)
        (proxima-posicao-homem nil)
        (filhos 0)
        (aux nil))
    (dotimes (i (list-length (first estado)))
      (let ((caminho nil)
            (caixa (nth i (first estado)))
            (ocupadas (coloca-caixotes (limpa-mapa-aux *mapa-reversed*) (first estado))))
        (dolist (jogada (jogadas-validas2 (mapa-sokoban-mapa *mapa-reversed*) ocupadas (first caixa) (second caixa)))
          (block processa-jogadas
                 (setf novo-estado (copy-estado estado))
                 (setf pos-diff (list (- (first jogada) (first caixa)) (- (second jogada) (second caixa))))
                 (setf proxima-posicao-homem (list (+ (first jogada) (first pos-diff)) (+ (second jogada) (second pos-diff))))
                 (let ((tunnel-res (tunnel-2 (first estado) caixa jogada)))
                   (unless (null tunnel-res)
                     (setf (nth i (first novo-estado)) (first tunnel-res))
                     (setf proxima-posicao-homem (second tunnel-res))
                     (if (= (list-length (second estado)) 1)
                         (setf caminho (third tunnel-res))
                         (progn
                           (setf caminho nil)
                           (setf caminho (encontra-caminho *mapa-reversed* (first estado) (first jogada) (second jogada) (first homem) (second homem)))
                           (when (null caminho)
                             (return-from processa-jogadas nil))
                           (setf caminho (nconc (third tunnel-res) (cdr caminho)))))
                     (unless (or (null caminho)
                                 (player-surrounded? (first novo-estado) proxima-posicao-homem))
                       (incf filhos)
                       (push proxima-posicao-homem caminho)
                       (setf (second novo-estado) (nconc caminho (cdr (second novo-estado))))
                       (setf aux (cons jogada aux))
                       (setf sucessores (cons novo-estado sucessores)))))))))
    (unless (= filhos 0)
      (setf *children* (+ *children* filhos))
      (setf *parents* (1+ *parents*)))
    (unless (null aux)
      (let* ((estado-jogadas-ordenados (list (ordena-lista (first estado)) (ordena-lista aux)))
             (hash-value (gethash (sxhash estado-jogadas-ordenados) *estados-gerados-reversed*)))
        (when (null hash-value)
          (setf (gethash (sxhash estado-jogadas-ordenados) *estados-gerados-reversed*) t)
          (dolist (e sucessores)
            (push e *gerados-reversed*))
          sucessores)))))


(defun compara-posicoes-caixas (estado1 estado2)
  (equalp (car estado1) (car estado2)))


(defun casa-preenchida (mapa i j)
  (aref mapa i j))

(defun quicksort (l)
  "Quicksort divides all elements into smaller or larger than the first element.
  These are then sorted recursivly with the first element in the middle"
  (if (null l) nil                      ; Recursive case
      (labels ((bigger-el (x) (or (and (not (< (first x) (first (first l)))) (> (first x) (first (first l)))) (> (second x) (second (first l)))))) ; t if x > first
              (let ((smaller (remove-if #'bigger-el (rest l))) ; all < first
                    (bigger  (remove-if-not #'bigger-el (rest l)))) ; all > first
                (append (quicksort smaller) (list (first l)) (quicksort bigger))))))


(defun elimina-cantos (estrutura)
  (let* ((mapa (mapa-sokoban-mapa estrutura))
         (linhas (mapa-sokoban-nlinhas estrutura))
         (colunas (mapa-sokoban-ncolunas estrutura))
         (destinos (mapa-sokoban-destinos estrutura))
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


(defun resolve-sokoban (filename tipo-procura
                                 &key (profundidade-maxima most-positive-fixnum)
                                 (espaco-em-arvore? nil))
  
  (flet ((faz-a-procura (problema tipo-procura
                                  profundidade-maxima espaco-em-arvore?
                                  &key (problema-normal nil))
                        (cond ((and (string-equal tipo-procura "bidirectional") (not (null problema-normal)))
                               (bidirectional problema-normal problema))
                              ((string-equal tipo-procura "largura")
                               (largura-primeiro problema :espaco-em-arvore? espaco-em-arvore?))
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
        
        (let* ((*nos-gerados* 0)
               (*nos-expandidos* 0)
               (estado-inicial (parse-ficheiro filename))
               (estado-inicial-reversed nil)
               (problema-normal nil)
               (problema-reversed nil)
               (destinos nil)
               (caixas nil)
               (homem nil)
               (caminho nil)
               (resultado nil))
          
          (setf *parents* 0.0)
          (setf *children* 0.0)
          (setf *estados-gerados-normal* (make-hash-table :test 'equal))
          (setf *estados-gerados-reversed* (make-hash-table :test 'equal))
          (setf *gerados-reversed* nil)
          (setf *bidirectional-match* nil)
          (setf *mapa-normal* (copy-structure-sokoban (first estado-inicial)))
          (setf *mapa-reversed* (first estado-inicial))
          (setf *mapa-cantos* (elimina-cantos *mapa-normal*))
          
          (setf destinos (copy-list (mapa-sokoban-destinos *mapa-reversed*)))
          (setf caixas (copy-list (second estado-inicial)))
          (setf homem (copy-list (third estado-inicial)))
          (setf *posicoes-caixas-originais* caixas)
          (setf *posicao-homem-original* homem)
          
          (setf estado-inicial (cdr estado-inicial))
          (setf (second estado-inicial) (list (second estado-inicial)))
          (setf estado-inicial-reversed (copy-list estado-inicial))
          (setf (mapa-sokoban-destinos *mapa-reversed*) caixas)
          (setf (first estado-inicial-reversed) destinos)
          
          (setf problema-normal (cria-problema estado-inicial
                                        (list #'operador)
                                        :objectivo? #'objectivo
                                        :heuristica #'h2-normal))
          (setf problema-reversed (cria-problema estado-inicial-reversed
                                                 (list #'reversed-operator)
                                                 :objectivo? #'objectivo-reversed
                                                 :heuristica #'h1-reversed))
          
          (setf caminho (faz-a-procura problema-reversed
                                       tipo-procura
                                       profundidade-maxima
                                       espaco-em-arvore?
                                       :problema-normal problema-normal))
          
          ;(setf resultado (faz-caminho-normal caminho))
          (if (or (string-equal tipo-procura "bidirectional")
                  (string-equal tipo-procura "melhor.abordagem"))
              (setf resultado (faz-caminho-bidirectional caminho))
              (setf resultado (faz-caminho-reversed caminho caixas homem)))
          
          ;     (format t "============================
          ;   NÓS EXPANDIDOS: ~A
          ;   NÓS GERADOS: ~A
          ;   PROFUNDIDADE ATINGIDA: ~A
          ;   CUSTO: ~A
          ;   FACT. MÉD. RAMIFIC.: ~A
          ; ============================~%"
          ;                *nos-gerados*
          ;                *nos-expandidos*
          ;                (list-length caminho)
          ;                (list-length resultado)
          ;                (/ *children* *parents*))
          resultado)))





