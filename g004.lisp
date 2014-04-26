;(in-package :user)

(compile-file "sokoban.lisp")
(load "sokoban")
(compile-file "procura.lisp")
(load "procura")
(compile-file "procuras.lisp")
(load "procuras")

(defun passos (caminho)
	(reverse (third (first (last caminho)))))



(defun objectivo (estado)
	(let* ((mapa (first estado))
			(caixotes (second estado))
			(posicoes-certas 0))
	(dotimes (i (length caixotes))
		(dolist (p caixotes)
			(when (equal p (nth i (mapa-sokoban-destinos mapa)))
				(incf posicoes-certas))))
	(= posicoes-certas (length caixotes))))

(defun copy-estado (estado)
	(let ((copy (make-mapa-sokoban))
			(mapa (first estado))
			(caixas (copy-list (second estado)))
			(pos (copy-list (third estado))))
		(setf (mapa-sokoban-mapa copy) (copy-array (mapa-sokoban-mapa mapa)))
		(setf (mapa-sokoban-destinos copy) (copy-list (mapa-sokoban-destinos mapa)))
		(setf (mapa-sokoban-mapa-aux copy) (copy-array (mapa-sokoban-mapa-aux mapa)))
		(setf (mapa-sokoban-nlinhas copy) (mapa-sokoban-nlinhas mapa))
		(setf (mapa-sokoban-ncolunas copy) (mapa-sokoban-ncolunas mapa))
		(list copy caixas pos)))


(defun jogadas-validas3 (mapa ocupadas x y)
  (let ((res nil))
    (unless (or (aref mapa (1+ x) y) (aref ocupadas (1+ x) y) (aref mapa (1- x) y) (aref ocupadas (1- x) y))
    	(push (list (1+ x) y) res)
    	(push (list (1- x) y) res))
    (unless (or (aref mapa x (1+ y)) (aref ocupadas x (1+ y)) (aref mapa x (1- y)) (aref ocupadas x (1- y)))
    	(push (list x (1+ y)) res)
    	(push (list x (1- y)) res))
    res))


(defun operador (estado)
	(let* ((mapa (mapa-sokoban-mapa (first estado)))
		  	(novo-estado nil)
		  	(proxima-posicao nil)
		  	(sucessores nil)
		  	(homem (first (third estado))))
		(dotimes (i (length (second estado)))
			(let ((caixa (nth i (second estado)))
					(caminho nil)
		  			(ocupadas (coloca-caixotes (limpa-mapa-aux (first estado)) (second estado))))
				(dolist (jogada (jogadas-validas3 mapa ocupadas (first caixa) (second caixa)))
					(when (ha-caminho (first estado) (second estado) (first homem) (second homem) (first jogada) (second jogada))
						(setf novo-estado (copy-estado estado))
						(setf proxima-posicao (list (+ (- (first caixa) (first jogada)) (first caixa))
													(+ (- (second caixa) (second jogada)) (second caixa))))
						(setf (nth i (second novo-estado)) proxima-posicao)
						(setf caminho (encontra-caminho (first estado) (second estado) (first homem) (second homem) (first jogada) (second jogada)))
						(setf caminho (reverse caminho))
						(push caixa caminho)
						(setf (third novo-estado) (nconc caminho (cdr (third novo-estado))))
						(setf sucessores (cons novo-estado sucessores))))))
		sucessores))


(defun resolve-sokoban (filename tipo-procura)
	(let* ((estado-inicial (parse-ficheiro filename))
			(problema nil)
			(caminho nil))
			(setf (third estado-inicial) (list (third estado-inicial)))
			(setf problema (cria-problema estado-inicial
							(list #'operador)
							:objectivo? #'objectivo))
			(setf caminho (first (procura problema tipo-procura)))
		(passos caminho)))
