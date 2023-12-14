#lang racket/base

(require racket/cmdline
         racket/flonum)

(define (Approximate n)
  (let ([u (make-flvector n 1.0)]
        [v (make-flvector n 0.0)])
    (for ([i (in-range 10)])
      (MultiplyAtAv n u v)
      (MultiplyAtAv n v u))
    
    (let loop ([i 0][vBv 0.0][vv 0.0])
      (if (= i n)
          (flsqrt (fl/ vBv vv))
          (let ([vi (flvector-ref v i)])
            (loop (add1 i)
                  (fl+ vBv (fl* (flvector-ref u i) vi))
                  (fl+ vv (fl* vi vi))))))))

(define (A i j)
  (fl/ 1.0 (fl+ (fl* (->fl (+ i j))
                     (fl/ (->fl (+ i (+ j 1))) 2.0)) 
                (->fl (+ i 1)))))

(define (MultiplyAv n v Av)
  (for ([i (in-range n)])
    (flvector-set! Av i 
                   (for/fold ([r 0.0])
                       ([j (in-range n)])
                     (fl+ r (fl* (A i j) (flvector-ref v j)))))))

(define (MultiplyAtv n v Atv)
  (for ([i (in-range n)])
    (flvector-set! Atv i
                   (for/fold ([r 0.0])
                       ([j (in-range n)])
                     (fl+ r (fl* (A j i) (flvector-ref v j)))))))

(define (MultiplyAtAv n v AtAv)
  (let ([u (make-flvector n 0.0)])
    (MultiplyAv n v u)
    (MultiplyAtv n u AtAv)))

(printf "~a\n"
        (real->decimal-string
         (Approximate (command-line #:args (n) (string->number n)))
         9))
