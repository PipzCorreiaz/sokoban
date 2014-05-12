;(in-package :user)

(defvar *mapa*)
(defvar *mapa-cantos*)
(defvar *todos-estados-gerados* (make-hash-table :test 'equal))
(defvar *posicoes-caixas-originais*)
(defvar *posicao-homem-original*)

(compile-file "sokoban.lisp")
(load "sokoban")
(compile-file "procura.lisp")
(load "procura")
(compile-file "procuras.lisp")
(load "procuras")

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


; (defun jogadas-validas4 (estado ocupadas x y)
;   (let ((mapa (mapa-sokoban-mapa *mapa*))
;         (destinos (mapa-sokoban-destinos *mapa*))
;         (res nil)
;         (ocupadinhas nil)
;         (resultadinho nil))
;     (unless (or (aref mapa (1+ x) y) (aref ocupadas (1+ x) y) (aref mapa (1- x) y) (aref ocupadas (1- x) y))
;     	(setf ocupadinhas (copy-array ocupadas))
;      	(setf (aref ocupadinhas x y) nil)
;       	(setf resultadinho (jogadas-validas3 mapa ocupadinhas (1+ x) y))
;       	(when (or (destino? destinos (1+ x) y) (>= (length resultadinho) 2))
;     		(push (list (1- x) y) res))
;        	(setf ocupadinhas (copy-array ocupadas))
;      	(setf (aref ocupadinhas x y) nil)
;       	(setf resultadinho (jogadas-validas3 mapa ocupadinhas (1- x) y))
;       	(when (or (destino? destinos (1- x) y) (>= (length resultadinho) 2))
;     		(push (list (1+ x) y) res)))
;     (unless (or (aref mapa x (1+ y)) (aref ocupadas x (1+ y)) (aref mapa x (1- y)) (aref ocupadas x (1- y)))
;       	(setf ocupadinhas (copy-array ocupadas))
;      	(setf (aref ocupadinhas x y) nil)
;       	(setf resultadinho (jogadas-validas3 mapa ocupadinhas x (1+ y)))
;       	(when (or (destino? destinos x (1+ y)) (>= (length resultadinho) 2))
;     		(push (list x (1- y)) res))
;        	(setf ocupadinhas (copy-array ocupadas))
;      	(setf (aref ocupadinhas x y) nil)
;       	(setf resultadinho (jogadas-validas3 mapa ocupadinhas x (1- y)))
;       	(when (or (destino? destinos x (1- y)) (>= (length resultadinho) 2))
;     		(push (list x (1+ y)) res)))
;     res))

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
            (when (or (destino? destinos next-pos (cadr caixa)) (aref mapa (+ (car caixa) (* (1+ i) diff-l)) (cadr caixa)) (not (and (aref mapa next-pos parede1) (aref mapa next-pos parede2))))
              (return-from tunnel (list (list next-pos (cadr caixa)) caminho)))
            (setf i (1+ i))))
        (loop
          (let ((next-pos (+ (cadr caixa) (* i diff-c))))
            (setf parede1 (1- (car caixa)))
            (setf parede2 (1+ (car caixa)))
            (when (or (destino? destinos next-pos (cadr caixa)) (aref mapa (car caixa) (+ (cadr caixa) (* (1+ i) diff-c))) (not (and (aref mapa parede1 next-pos) (aref mapa parede2 next-pos))))
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

(defun jogadas-muito-validas (ocupadas caixa)
  (let* ((mapa (mapa-sokoban-mapa *mapa*))
         (n-linhas (mapa-sokoban-nlinhas *mapa*))
         (n-colunas (mapa-sokoban-ncolunas *mapa*))
         (jv (jogadas-validas2 (mapa-sokoban-mapa *mapa*) ocupadas (first caixa) (second caixa)))
         (res nil))
    (dolist (jogada jv)
      (let ((i 1)
            (diff-l (- (car jogada) (car caixa)))
            (diff-c (- (cadr jogada) (cadr caixa)))
            (caminho nil))
        (if (= diff-l 0)
            (block loopjogadal
                   (loop
                     (let ((coluna (+ (cadr caixa) (* i diff-c))))
                       (when (or (aref mapa (car caixa) coluna)
                                 (> coluna (- n-colunas 2))
                                 (< coluna 2))
                         (return-from loopjogadal))
                       (setf caminho (cons (list (car caixa) coluna) caminho))
                       (setf res (cons (list jogada
                                             (list (car caixa) coluna)
                                             (cons (list (car caixa) (+ (cadr caixa) (* (1+ i) diff-c))) caminho))
                                       res))
                       (setf i (1+ i)))))
            (block loopjogadac
                   (loop
                     (let ((linha (+ (car caixa) (* i diff-l))))
                       (when (or (aref mapa linha (cadr caixa))
                                 (> linha (- n-linhas 2))
                                 (< linha 2))
                         (return-from loopjogadac))
                       (setf caminho (cons (list linha (cadr caixa)) caminho))
                       (setf res (cons (list jogada
                                             (list linha (cadr caixa))
                                             (cons (list (+ (car caixa) (* (1+ i) diff-l)) (cadr caixa)) caminho))
                                       res))
                       (setf i (1+ i))))))))
    res))

(defun reversed-operator (estado)
  (let ((novo-estado nil)
        (proxima-posicao nil)
        (sucessores nil)
        (homem (first (second estado)))
        (pos-diff nil)
        (proxima-posicao-homem nil)
        (aux nil))
    (dotimes (i (length (first estado)))
      (let ((caixa (nth i (first estado)))
            (ocupadas (coloca-caixotes (limpa-mapa-aux *mapa*) (first estado))))
        (dolist (jogada-caminho (jogadas-muito-validas ocupadas caixa))
          (let* ((jogada (first jogada-caminho))
                 (proxima-posicao-caixa (second jogada-caminho))
                 (caminho nil)
                 (proxima-posicao-homem (car (third jogada-caminho))))
            (setf ocupadas (coloca-caixotes (limpa-mapa-aux *mapa*) (first estado)))
            (setf novo-estado (copy-estado estado))
            (unless (or (casa-preenchida ocupadas (first proxima-posicao-homem) (second proxima-posicao-homem)) (casa-ocupada *mapa* (first proxima-posicao-homem) (second proxima-posicao-homem)))
              (setf (nth i (first novo-estado)) proxima-posicao-caixa)
              (if (= (list-length (second estado)) 1)
                  (setf caminho (list (list 999 999)))
                  (setf caminho (reverse (encontra-caminho *mapa* (first estado) (first homem) (second homem) (first jogada) (second jogada)))));))
              (unless (or (null caminho)
                          (player-surrounded? (first novo-estado) proxima-posicao-homem))
                (setf caminho (nconc (copy-list (third jogada-caminho)) (cdr caminho)))
                (setf (second novo-estado) (nconc caminho (cdr (second novo-estado))))
                (setf aux (cons jogada aux))
                (setf sucessores (cons novo-estado sucessores))))))))
    (when (not (gethash (list (sort (first estado) #'list<) (sort aux #'list<)) *todos-estados-gerados*))
      (setf (gethash (list (first estado) aux) *todos-estados-gerados*) t)
      sucessores)))

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
      (nconc caminho-encontrado (cdr novo-caminho)))))


(defun resolve-sokoban (filename tipo-procura)
  (let* ((estado-inicial (parse-ficheiro filename))
         (problema nil)
         (destinos nil)
         (caixas nil)
         (homem nil)
         (caminho nil))
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
                                  :heuristica #'h1-alt
                                  :estado= #'compara-estado))
    (setf caminho (first (procura problema tipo-procura)))
    ;(passos caminho)))
    (novos-passos caminho caixas homem)))


(defun remove-nth (lst index)
  (if (= index 0)
      (cdr lst)
      (cons (car lst) (remove-nth (cdr lst) (1- index)))))

