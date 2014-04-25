
;(in-package :user)

(defconstant +parede-in+ #\#)
(defconstant +destino-in+ #\.)
(defconstant +caixote-in+ #\$)
(defconstant +caixote-no-sitio-in+ #\*)
(defconstant +jogador-in+ #\@)


(defstruct mapa-sokoban
  (mapa nil)
  (destinos nil)
  (mapa-aux nil)
  (nlinhas nil)
  (ncolunas nil))


(defun casa-ocupada (mapa i j)
  (aref (mapa-sokoban-mapa mapa) i j))


(defun le-linhas (ifile)
  (let ((res nil)
	(linha nil))
    (loop
     (setf linha (read-line ifile NIL NIL))
     (unless linha (return))
     (push linha res))
    (reverse res)))


(defun comprimento-maximo (linhas)
  (reduce #'max (mapcar #'length linhas)))


(defun parse-ficheiro (filename)
  (with-open-file (ifile filename :direction :input :if-does-not-exist nil)
      (if (null ifile)
	(format T "O Ficheiro ~A nao existe!~&" filename) 
	(let* ((linhas (le-linhas ifile))
	       (dims (list (length linhas) (comprimento-maximo linhas)))
	       (novo (make-mapa-sokoban
		      :mapa (make-array dims
				 :initial-element nil)
		      :mapa-aux (make-array dims
				 :initial-element nil)
		      :nlinhas (first dims)
		      :ncolunas (second dims)))
	       (caixotes nil)
	       (pos-inicial nil))
	  (dotimes (i (length linhas) (list novo caixotes pos-inicial))
	    (let ((linha (nth i linhas)))
	      (dotimes (j (length linha))
		(cond ((char= (aref linha j) +parede-in+)
		       (setf (aref (mapa-sokoban-mapa novo) i j) T))
		      ((char= (aref linha j) +caixote-no-sitio-in+)
		       (push (list i j) caixotes)
		       (push (list i j) (mapa-sokoban-destinos novo)))
		      ((char= (aref linha j) +caixote-in+)
		       (push (list i j) caixotes))
		      ((char= (aref linha j) +destino-in+)
		       (push (list i j) (mapa-sokoban-destinos novo)))
		      ((char= (aref linha j) +jogador-in+)
		       (setf pos-inicial (list i j)))))))))))


(defun coloca-caixotes (mapa caixotes)
  (dolist (elm caixotes mapa)
    (setf (aref mapa (first elm) (second elm)) T)))


(defun limpa-mapa-aux (mapa)
  (dotimes (l (mapa-sokoban-nlinhas mapa))
    (dotimes (c (mapa-sokoban-ncolunas mapa))
      (setf (aref (mapa-sokoban-mapa-aux mapa) l c) nil)))
  (mapa-sokoban-mapa-aux mapa))


(defun ha-caminho (mapa ocupadas x1 y1 x2 y2)
  (ha-caminho-aux (mapa-sokoban-mapa mapa)
		  (coloca-caixotes (limpa-mapa-aux mapa)
				   ocupadas)
		  (list x1 y1)
		  x2 y2))


(defun jogadas-validas (mapa ocupadas x y res)
  (unless (or (aref mapa (1+ x) y) (aref ocupadas (1+ x) y)) (setf res (cons (1+ x) (cons y res))))
  (unless (or (aref mapa x (1+ y)) (aref ocupadas x (1+ y))) (setf res (cons x (cons (1+ y) res))))
  (unless (or (aref mapa (1- x) y) (aref ocupadas (1- x) y)) (setf res (cons (1- x) (cons y res))))
  (unless (or (aref mapa x (1- y)) (aref ocupadas x (1- y))) (setf res (cons x (cons (1- y) res))))
  res)


(defun ha-caminho-aux (mapa ocupadas inicial xdest ydest)
  (if (NULL inicial)
    nil
    (let ((x (first inicial))
	  (y (second inicial)))
      (cond ((and (= x xdest) (= y ydest)) T)
	    (T (setf (aref ocupadas x y) T)
	       (ha-caminho-aux mapa ocupadas
			       (jogadas-validas mapa ocupadas x y (cddr inicial))
			       xdest ydest))))))


(defun encontra-caminho (mapa ocupadas x1 y1 x2 y2)
  (encontra-caminho-aux (mapa-sokoban-mapa mapa)
		  (coloca-caixotes (make-array (array-dimensions (mapa-sokoban-mapa mapa))
					       :initial-element NIL)
			  ocupadas)
		  (list x1 y1)
		  x2 y2))


(defun jogadas-validas2 (mapa ocupadas x y)
  (let ((res nil))
    (unless (or (aref mapa (1+ x) y) (aref ocupadas (1+ x) y)) (push (list (1+ x) y) res))
    (unless (or (aref mapa x (1+ y)) (aref ocupadas x (1+ y))) (push (list x (1+ y)) res))
    (unless (or (aref mapa (1- x) y) (aref ocupadas (1- x) y)) (push (list (1- x) y) res))
    (unless (or (aref mapa x (1- y)) (aref ocupadas x (1- y))) (push (list x (1- y)) res))
    res))


(defun encontra-caminho-aux (mapa ocupadas inicial xdest ydest)
  (if (null inicial)
    nil
    (let ((x (first inicial))
	  (y (second inicial)))
      (cond ((and (= x xdest) (= y ydest)) (list (list x y)))
	    (T (setf (aref ocupadas x y) T)
	       (dolist (elm (jogadas-validas2 mapa ocupadas x y) NIL)
		 (let ((res (encontra-caminho-aux mapa ocupadas elm xdest ydest)))
		   (when res (return-from encontra-caminho-aux (cons (list x y) res))))))))))
  




