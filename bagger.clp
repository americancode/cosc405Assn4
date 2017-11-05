(deftemplate item
    (slot name)
    (slot bottle)
    (slot size)
    (slot crushable)
)

(deftemplate bag
    (slot number)
    (slot weight)
    (slot bottle)
)

(deffacts order2
    (item (name granola1) (bottle no) (size 4) (crushable no))
    (item (name granola2) (bottle no) (size 4) (crushable no))
    (item (name granola3) (bottle no) (size 4) (crushable no))
    (item (name tuna1) (bottle no) (size 1) (crushable no))
    (item (name tuna2) (bottle no) (size 1) (crushable no))
    (item (name tuna3) (bottle no) (size 1) (crushable no))
    (item (name tuna4) (bottle no) (size 1) (crushable no))
    (item (name iceCream1) (bottle no) (size 2) (crushable no))
    (item (name iceCream2) (bottle no) (size 2) (crushable no))
    (item (name bread1) (bottle no) (size 2) (crushable yes))
    (item (name bread2) (bottle no) (size 2) (crushable yes))
    (item (name potato-chips) (bottle no) (size 2) (crushable yes))
    (item (name glop1) (bottle no) (size 1) (crushable no))
    (item (name glop2) (bottle no) (size 1) (crushable no))
    (item (name glop) (bottle no) (size 1) (crushable no))
    (item (name milk1) (bottle yes) (size 4) (crushable no))
    (item (name milk2) (bottle yes) (size 4) (crushable no))



)

;Checking the order
(defrule start
    ?i <- (initial-fact)
=>
    (printout t "Select order (1 or 2): ")
    (bind ?order (read))
    (if (eq ?order 1)
            then (load "order1.txt")
            else (load "order2.txt")
    )
    (printout t crlf)
    (retract ?i)
    (assert (pepsi no))
    (assert (step check-order))
    (assert (bag (number 1) (weight 0) (bottle no)))
    (assert (lastBagNum 1))
)


(defrule B1
    (step check-order)
    (item (name pepsi))
    ?pep <- (pepsi no)
    =>
    (retract ?pep)
    (assert (pepsi yes))
)


(defrule B2
    (step check-order)
    (item (name potato-chips))
    ?pep <- (pepsi no)
    =>
    (printout t "Do you want a Pepsi to wash down those chips:  ")
    (bind ?answer (read))
    (if (eq ?answer y)
        then
            (printout t "Add a Pepsi to the oder" crlf)
            (assert (item (name pepsi) (bottle yes) (size 4) (crushable yes)))

    )
    (retract ?pep)
    (assert (pepsi yes))
)


(defrule B3
    ?step <- (step check-order)
    =>
    (printout t "Begin bagging LARGE items" crlf)
    (retract ?step)
    (assert (step bag-large-items))
)

;rules for large bagging
(defrule B4
    (step bag-large-items)
    ?item <- (item (name ?n) (bottle yes) (size 4)) ;a large item with bottle
    ?bag <- (bag (number ?bn) (weight ?bw) (bottle no)) ;a bag with room for large item and no bottle
    (test (<= ?bw 8))
    =>
    (printout t "Place " ?n" in bag # " ?bn crlf)
    (assert (bag (number ?bn) (weight (+ ?bw 4)) (bottle yes)))
    (retract ?bag)
    (retract ?item)
)

(defrule B5
    (step bag-large-items)
    ?item <- (item (name ?n) (bottle no) (size 4)) ;large item that is not a bottle
    ?bag <- (bag (number ?bn) (weight ?bw) (bottle ?bot)) ;bag with room for large item
    (test (<= ?bw 8))
    =>
    (printout t "Place " ?n" in bag # " ?bn crlf)
    (retract ?bag)
    (retract ?item)
    (assert (bag (number ?bn) (weight (+ ?bw 4)) (bottle ?bot)))
)

(defrule B6 ;New bag rule for large items
    (step bag-large-items)
    ?item <- (item (name ?n) (size 4))
    ?bRule <- (lastBagNum ?bn)
    =>
    (printout t crlf)
    (printout t "Starting a new Bag" crlf)
    (retract ?bRule)
    (assert (lastBagNum (+ ?bn 1)))
    (assert (bag (number (+ ?bn 1)) (weight 0) (bottle no)))
)

(defrule B7
    ?step <- (step bag-large-items)
    =>
    (printout t crlf crlf)
    (printout t "Begin bagging MEDIUM items" crlf)
    (retract ?step)
    (assert (step bag-medium-items))
)

;rules for bagging medium items
(defrule B8
    (step bag-medium-items)
    ?item <- (item (name ?iName) (size 2) (crushable no)) ;a noncrushable medium item
    ?bag <- (bag (number ?bNumber) (weight ?bWeight) (bottle ?bot)) ;a bag with room for a medium item
    (test (<= ?bWeight 10))
    =>
    (printout t "Place " ?iName" in bag # " ?bNumber crlf)
    (assert (bag (number ?bNumber) (weight (+ ?bWeight 2)) (bottle ?bot)))
    (retract ?item)
    (retract ?bag)
)

(defrule B9 ;New bag rule for medium items
    (step bag-medium-items)
    ?item <- (item (size 2) (crushable no)) ;a noncrushable medium item
    ?bRule <- (lastBagNum ?bn)
    =>
    (printout t crlf)
    (printout t "Starting a new Bag" crlf)
    (assert (lastBagNum (+ ?bn 1)))
    (assert (bag (number (+ ?bn 1)) (weight 0) (bottle no)))
    (retract ?bRule)
)

(defrule B10
    ?step <- (step bag-medium-items)
    =>
    (printout t crlf crlf)
    (printout t "Begin bagging SMALL items" crlf)
    (retract ?step)
    (assert (step bag-small-items))
)

;Rules for small items
(defrule B11
    (step bag-small-items)
    ?item <- (item (name ?iName) (size 1)) ; a small item
    ?bag <- (bag (number ?bNumber) (weight ?bWeight) (bottle ?bot)) ;a bag with room for a small item
    (test (<= ?bWeight 11))
    =>
    (printout t "Place " ?iName" in bag # " ?bNumber crlf)
    (assert (bag (number ?bNumber) (weight (+ ?bWeight 1)) (bottle ?bot)))
    (retract ?item)
    (retract ?bag)
)

(defrule B12 ; Rule for making new bag
    (step bag-small-items)
    ?item <- (item (size 1)) ;a small item
    ?bRule <- (lastBagNum ?bn)
    =>
    (printout t crlf)
    (printout t "Starting a new bag" crlf)
    (assert (lastBagNum (+ ?bn 1)))
    (assert (bag (number ( + ?bn 1)) (weight 0) (bottle no)))
    (retract ?bRule)
)

(defrule B13
    ?step <-(step bag-small-items)
    =>
    (retract ?step)
    (assert (step bag-crushable-items))
    (printout t crlf)
    (printout t "Begin bagging CRUSHABLE items " crlf)
)

;Rules for bagging crushable items
(defrule B15
    (step bag-crushable-items)
    ?item <- (item (name ?iName) (crushable yes)) ;a crushable item
    ?bag <- (bag (number ?bNumber) (weight ?bWeight) (bottle ?bot)) ;a bag with room for a medium item
    (test (<= ?bWeight 10)) ;All crushable items: chips and bread are medium so this test works.
    =>
    (printout t "Place " ?iName" in bag # " ?bNumber crlf)
    (assert (bag (number ?bNumber) (weight (+ ?bWeight 1)) (bottle ?bot)))
    (retract ?item)
    (retract ?bag)
)


(defrule B14 ;Rule for making new bag
    (step bag-crushable-items)
    ?item <- (item (crushable yes)) ;a small item
    ?bRule <- (lastBagNum ?bn)
    =>
    (printout t crlf)
    (printout t "Starting a new bag" crlf)
    (assert (lastBagNum (+ ?bn 1)))
    (assert (bag (number ( + ?bn 1)) (weight 0) (bottle no)))
    (retract ?bRule)
)

;Rule for ending bagging
(defrule B16
    ?step <-(step bag-crushable-items)
    =>
    (retract ?step)
    (printout t "Bagging is complete" crlf)
)
