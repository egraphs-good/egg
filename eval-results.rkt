#lang racket

(require "eval-library.rkt")
(require plot/no-gui)

(define (getter symbol)
  (define names `(start-expr
                  end-expr
                  vanilla-duration
                  greedy-duration
                  proof-length greedy-proof-length dag-size
                  greedy-dag-size z3-duration
                  z3-dag-size
                  egg-run-duration
                  upwards-run-duration
                  upwards-proof-length
                  upwards-dag-size))
  (define m
    (for/hash ([name names] [i (in-range 0 (length names))])
              (values name (curryr list-ref i))))
              
  (hash-ref m symbol))

(define (output-results-with-tag output-port content tag getter-normal getter-greedy length-str)
  (define (output name val #:output-percent [output-percent #f])
    (output-latex-macro (string-append length-str "-" name "-" tag) val output-port #:output-percent output-percent))
  (define vanilla-lengths (get-sum content (getter getter-normal)))
  (define greedy-lengths (get-sum content (getter getter-greedy)))

  
  (define num-smaller (get-sum content
                               (lambda (row)
                                 (if (> ((getter getter-normal) row)
                                        ((getter getter-greedy) row))
                                     1 0))))
  (define num-smaller-than-half
    (get-sum content
             (lambda (row)
               (if (> ((getter getter-normal) row)
                      (* 2 ((getter getter-greedy) row)))
                   1 0))))
  
  (output "vanilla-sum" vanilla-lengths)
  (output "greedy-sum" greedy-lengths)
  (when (> (length content) 0)
        (output "percent-greedy-smaller-than-vanilla" (/ num-smaller (length content))
          #:output-percent #t)
        (output "percent-greedy-smaller-than-half-vanilla" (/ num-smaller-than-half (length content))
                #:output-percent #t)
        (output "percent-greedy-reduction" (/ (- vanilla-lengths greedy-lengths) vanilla-lengths)
                #:output-percent #t)))

(define (output-macro-results output-port content getter-normal getter-greedy length-str)
  (define filtered-greater-than-10
    (filter (lambda (row) (> ((getter getter-normal) row) 10)) content))
  (define filtered-greater-than-50
    (filter (lambda (row) (> ((getter getter-normal) row) 50)) content))
  (output-results-with-tag output-port content "" getter-normal getter-greedy length-str)
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-10 "length-grt-10" getter-normal getter-greedy length-str)
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-50 "length-grt-50" getter-normal getter-greedy length-str))

(define (make-proof-len-scatter output-file cutoff results getter-normal getter-greedy x-str y-str)
  (define scatter-points (points
                          #:alpha 0.5
                          #:color "blue"
                          #:size 2
                          #:x-max cutoff
                          #:y-max cutoff
                          
                  (list->vector
                  (map (lambda (row)
                        (vector ((getter getter-normal) row)
                                ((getter getter-greedy) row)))
                      results))))

  (parameterize-plot-size
   300
   1
   ""
   x-str
   y-str
   output-file
   (lambda ()
     (plot-pict
      (list  (function (λ (x) x) #:color 0 #:style 'dot)
             scatter-points)))))

(module+ main
  (command-line #:program "report"
                #:args (results-file report-dir)
    (define macro-output-file (build-path report-dir "macros.txt"))
    (define results (file->list results-file))
    (define filtered-z3 (filter (lambda (row) ((getter 'z3-dag-size) row))
                                results))
    
    (define macro-port (open-output-file macro-output-file #:exists 'replace))
    (output-macro-results macro-port
                          results 'proof-length 'greedy-proof-length "proof-length")
    (println "" macro-port)
    (output-macro-results macro-port
                          results 'dag-size 'greedy-dag-size "dag-size")
    (println "" macro-port)
    (output-macro-results macro-port
                          filtered-z3 'z3-dag-size 'greedy-dag-size "z3-dag-size")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter.png") #f results 'proof-length 'greedy-proof-length "Unoptimized Proof Lengths" "Greedily Optimized Proof Lengths")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter-zoomed800.png") 800 results 'proof-length 'greedy-proof-length "Unoptimized Proof Lengths" "Greedily Optimized Proof Lengths")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter-zoomed200.png") 200 results 'proof-length 'greedy-proof-length "Unoptimized Proof Lengths" "Greedily Optimized Proof Lengths")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter.png") #f results 'dag-size 'greedy-dag-size "Unoptimized DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter-zoomed800.png") 800 results 'dag-size 'greedy-dag-size "Unoptimized DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter-zoomed200.png") 200 results 'dag-size 'greedy-dag-size "Unoptimized DAG Size" "Greedily Optimized DAG Size")

    (println (length filtered-z3))
    (println (length results))
    (make-proof-len-scatter (build-path report-dir "z3-dag-size-scatter.png") #f filtered-z3 'z3-dag-size 'greedy-dag-size "Z3 DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "z3-dag-size-scatter-zoomed200.png") 200 filtered-z3 'z3-dag-size 'greedy-dag-size "Z3 DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "z3-dag-size-scatter-zoomed100.png") 100 filtered-z3 'z3-dag-size 'greedy-dag-size "Z3 DAG Size" "Greedily Optimized DAG Size")

    (make-proof-len-scatter (build-path report-dir "rebuilding-upwards-zoomed100.png") 100 results 'dag-size 'upwards-dag-size "DAG Size With Rebuilding" "DAG Size With Upwards Merging")

    
  )
  )