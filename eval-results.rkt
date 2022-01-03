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
                  upwards-proof-duration
                  upwards-proof-length
                  upwards-dag-size
                  upwards-run-duration
                  low-greedy-time
                  low-optimal-time
                  low-greedy-tree-size
                  low-optimal-tree-size))
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

  (output "numbenchmarks" (length content))
  (output "vanillasum" vanilla-lengths)
  (output "sum" greedy-lengths)
  (when (> (length content) 0)
        (output "percentsmallerthanvanilla" (/ num-smaller (length content))
          #:output-percent #t)
        (output "percentsmallerthanhalfvanilla" (/ num-smaller-than-half (length content))
                #:output-percent #t)
        (output "percentreduction" (/ (- vanilla-lengths greedy-lengths) vanilla-lengths)
                #:output-percent #t)))

(define (output-macro-results output-port content getter-normal getter-greedy length-str)
  (define filtered-greater-than-10
    (filter (lambda (row) (> ((getter getter-normal) row) 10)) content))
  (define filtered-greater-than-50
    (filter (lambda (row) (> ((getter getter-normal) row) 50)) content))
  (output-results-with-tag output-port content "" getter-normal getter-greedy length-str)
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-10 "lengthgrtten" getter-normal getter-greedy length-str)
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-50 "lengthgrtfifty" getter-normal getter-greedy length-str))

(define (make-proof-len-scatter output-file cutoff results getter-normal getter-greedy x-str y-str)
  (define scatter-points (points
                          #:alpha 0.5
                          #:color "blue"
                          #:fill-color "blue"
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


(define (make-zach-graph output-file z3-unfiltered cutoff z3-dag-size-filter)
  (define z3-filtered
    (if z3-dag-size-filter
        (filter (lambda (row)
                  (>= z3-dag-size-filter ((getter 'z3-dag-size) row)))
                z3-unfiltered)
        z3-unfiltered))
  
  (define egg-rebuilding-greedy-points
    (points #:alpha 1
            #:color "green"
            #:sym 'circle
            #:size 4
            #:x-max cutoff
            (list->vector
             (map (lambda (row)
                    (vector (+ ((getter 'greedy-duration) row) ((getter 'egg-run-duration) row))
                            ((getter 'greedy-dag-size) row)))
                  z3-filtered))))

  (define z3-points
    (points #:alpha 1
            #:color "orange"
            #:sym 'triangle
            #:size 4
            #:x-max cutoff
            (list->vector
             (map (lambda (row)
                    (vector (+ ((getter 'z3-duration) row))
                            ((getter 'z3-dag-size) row)))
                  z3-filtered))))

  (define egg-rebuilding-points
    (points #:alpha 1
            #:color "blue"
            #:sym 'square
            #:size 4
            #:x-max cutoff
            (list->vector
             (map (lambda (row)
                    (vector (+ ((getter 'egg-run-duration) row) ((getter 'vanilla-duration) row))
                            ((getter 'dag-size) row)))
                  z3-filtered))))

  (define z3-timeout-points
    (points #:alpha 1
            #:color "red"
            #:sym 'triangle
            #:size 4
            (list->vector
             (map (lambda (row)
                    (vector cutoff
                             ((getter 'dag-size) row)))
                  
                  (filter (lambda (row)
                            (> ((getter 'z3-duration) row) (if cutoff cutoff 9999999999999)))
                          z3-filtered)))))

  (parameterize-plot-size
   300
   1
   ""
   "Time in Milliseconds"
   "DAG Size of Resulting Proof"
   output-file
   (lambda ()
     (plot-pict
      (list  
             egg-rebuilding-points
             egg-rebuilding-greedy-points
             z3-points
             z3-timeout-points)))))

(module+ main
  (command-line #:program "report"
                #:args (results-file report-dir)
    (define macro-output-file (build-path report-dir "macros.txt"))
    (define results (file->list results-file))
    (define filtered-z3 (filter (lambda (row) ((getter 'z3-dag-size) row))
                                results))
    (define filtered-upwards (filter (lambda (row) ((getter 'upwards-dag-size) row))
                                     results))
    (define filtered-optimal (filter (lambda (row) ((getter 'low-greedy-tree-size) row))
                                     results))
    
    (define macro-port (open-output-file macro-output-file #:exists 'replace))
    (output-macro-results macro-port
                          results 'proof-length 'greedy-proof-length "prooflength")
    (displayln "" macro-port)
    (output-macro-results macro-port
                          results 'dag-size 'greedy-dag-size "dagsize")
    (displayln "" macro-port)
    (output-macro-results macro-port
                          filtered-z3 'z3-dag-size 'greedy-dag-size "z3dagsize")

    (displayln "" macro-port)
    (output-macro-results macro-port
                          filtered-upwards 'dag-size 'upwards-dag-size "upwardsdagsize")

    (displayln "" macro-port)
    (output-macro-results macro-port
                          filtered-optimal 'low-greedy-tree-size 'low-optimal-tree-size "lowtreesize")

    


    (make-zach-graph (build-path report-dir "zach-graph.png")
                     filtered-z3 #f #f)
    (make-zach-graph (build-path report-dir "zach-graph-zoomed-2000.png")
                     filtered-z3 2000 #f)
    (make-zach-graph (build-path report-dir "zach-graph-filtered-z3-grt-20.png")
                     filtered-z3 #f 20)
    (make-zach-graph (build-path report-dir "zach-graph-filtered-z3-grt-20-zoomed-2000.png")
                     filtered-z3 2000 20)
                                 
    
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter.png") #f results 'proof-length 'greedy-proof-length "Unoptimized Proof Lengths" "Greedily Optimized Proof Lengths")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter-zoomed800.png") 800 results 'proof-length 'greedy-proof-length "Unoptimized Proof Lengths" "Greedily Optimized Proof Lengths")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter-zoomed200.png") 200 results 'proof-length 'greedy-proof-length "Unoptimized Proof Lengths" "Greedily Optimized Proof Lengths")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter.png") #f results 'dag-size 'greedy-dag-size "Unoptimized DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter-zoomed800.png") 800 results 'dag-size 'greedy-dag-size "Unoptimized DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter-zoomed200.png") 200 results 'dag-size 'greedy-dag-size "Unoptimized DAG Size" "Greedily Optimized DAG Size")

    (make-proof-len-scatter (build-path report-dir "optimal-tree-size-scatter.png") #f filtered-optimal 'low-greedy-tree-size 'low-optimal-tree-size "Greedily Optimized Tree Size" "Optimal Tree Size")

    (println (length filtered-z3))
    (println (length results))
    (make-proof-len-scatter (build-path report-dir "z3-dag-size-scatter.png") #f filtered-z3 'z3-dag-size 'greedy-dag-size "Z3 DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "z3-dag-size-scatter-zoomed200.png") 200 filtered-z3 'z3-dag-size 'greedy-dag-size "Z3 DAG Size" "Greedily Optimized DAG Size")
    (make-proof-len-scatter (build-path report-dir "z3-dag-size-scatter-zoomed100.png") 100 filtered-z3 'z3-dag-size 'greedy-dag-size "Z3 DAG Size" "Greedily Optimized DAG Size")

    (make-proof-len-scatter (build-path report-dir "rebuilding-upwards-zoomed100.png") 100 filtered-upwards 'dag-size 'upwards-dag-size "DAG Size With Rebuilding" "DAG Size With Upwards Merging")
    (make-proof-len-scatter (build-path report-dir "rebuilding-upwards-zoomed200.png") 200 filtered-upwards 'dag-size 'upwards-dag-size "DAG Size With Rebuilding" "DAG Size With Upwards Merging")

    (make-proof-len-scatter (build-path report-dir "z3-vs-rebuilding-greedy-time.png") #f filtered-z3 'z3-duration 'greedy-duration "Z3 Proof Production Runtime (ms)" "Greedy Proof Production Runtime (ms)")
    (make-proof-len-scatter (build-path report-dir "z3-vs-rebuilding-greedy-time-zoomed10000.png") 10000 filtered-z3 'z3-duration 'greedy-duration "Z3 Proof Production Runtime (ms)" "Greedy Proof Production Runtime (ms)")
    
    (make-proof-len-scatter (build-path report-dir "upwards-vs-rebuilding-greedy-zoomed-100.png") 100 filtered-upwards 'upwards-dag-size 'greedy-dag-size "DAG size with Upwards Merging" "DAG size with Rebuilding and Greedy Optimization")

    
  )
  )