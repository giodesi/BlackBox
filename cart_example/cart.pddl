(define (domain cart)
  (:requirements :strips :typing)
  (:types cargo place cart) 
  (:predicates
			 (at_crg ?c - cargo ?p - place)
			 (at_crt ?c - cart ?p - place)
			 (hasfuel ?c - cart)
			 (on ?c1 - cargo ?c2 - cart)
 )

(:action LOAD
   :parameters (?cr - cargo ?ct - cart ?p - place)
   :precondition (and
				(at_crg ?cr ?p) 
				(at_crt ?ct ?p))
   :effect (and
	    (on ?cr ?ct)
	    (not (at_crg ?cr ?p)))
)

(:action UNLOAD
   :parameters (?cr - cargo ?ct - cart ?p - place)
   :precondition (and
				(at_crt ?ct ?p) 
				(on ?cr ?ct))
   :effect (and
	    (at_crg ?cr ?p)
	    (not (on ?cr ?ct)))
)

(:action MOVE
   :parameters (?c - cart ?p1 ?p2 - place)
   :precondition (and
				(at_crt ?c ?p1) 
				(hasfuel ?c))
   :effect (and
	    (at_crt ?c ?p2)
	    (not (at_crt ?c ?p1))
		 (not (hasfuel ?c)))
)

)
