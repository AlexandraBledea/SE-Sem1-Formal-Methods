/* Concert
 * Author: night
 * Creation date: 1/10/2024
 */
MACHINE
    Concert
    
SEES
    String
    
USES
    Location
    
SETS
    CONCERT
    
ABSTRACT_VARIABLES
    concerts,
    concertId,
    concertDate,
    concertBookedTickets,
    concertLocation

INVARIANT
    concerts <: CONCERT &
    concertId : concerts >-> NATURAL1 &
    concertDate : concerts --> STR &
    concertBookedTickets : concerts --> NATURAL &
    concertLocation : concerts --> locations &
    /*5.	The number of tickets for a particular concert must not exceed the location’s capacity where it will take place. */
    ! con . (con : concerts => concertBookedTickets(con) <= locationCapacity(concertLocation(con)))
    
 
//    /* 2.	Multiple concerts can take place in the same location. However, the date of the concerts must not intersect each other. */
//    ! (con1 , con2) . ((con1 : concerts & con2 : concerts & concertLocation(con1) = concertLocation(con2) & con1 /= con2) => concertDate(con1) /= concertDate(con2))
 
    
INITIALISATION
    concerts,
    concertId,
    concertDate,
    concertBookedTickets,
    concertLocation := {}, {}, {}, {}, {}
    
OPERATIONS
    
    /* Create concert */
   
    newConcert <-- createConcert(dateValue, locationValue) =
    PRE
        dateValue : STR & 
        locationValue : locations &
        0 <= locationCapacity(locationValue) &
        /* 2.	Multiple concerts can take place in the same location. However, the date of the concerts must not intersect each other. */ 
        ! con . (con : concerts & concertLocation(con) = locationValue => concertDate(con) /= dateValue)
    THEN
        ANY con
        WHERE con : CONCERT - concerts
        THEN concerts := concerts \/ {con} ||
            ANY idValue
            WHERE idValue : NATURAL1 & idValue /: ran(concertId)
            THEN concertId(con) := idValue 
            END ||
            concertDate(con) := dateValue ||
            concertLocation(con) := locationValue ||
            concertBookedTickets(con) := 0 ||
            newConcert := con
        END
    END;
    
    
    
    
    
    /* Remove concert */
    removeConcert(concertValue) = 
    PRE
        concertValue : concerts
    THEN
        concerts := concerts - {concertValue} ||
        concertId := {concertValue} <<| concertId ||
        concertDate := {concertValue} <<| concertDate ||
        concertLocation := {concertValue} <<| concertLocation ||
        concertBookedTickets := {concertValue} <<| concertBookedTickets
    END;
    
    
    /* Remove all concerts from location */
    removeAllConcertsFromLocation(locationValue) = 
    PRE
        locationValue: locations
    THEN
        concerts := concerts - concertLocation~[{locationValue}] ||
        concertLocation := concertLocation |>> {locationValue} ||
        concertId := concertLocation~[{locationValue}] <<| concertId ||
        concertDate := concertLocation~[{locationValue}] <<| concertDate ||
        concertBookedTickets := concertLocation~[{locationValue}] <<| concertBookedTickets
    END;
    
    
    
    
    
    
    
    /* Increase booked tickets with 1 */
    increaseConcertBookedTickets(concertValue) =
    PRE
        concertValue : concerts &
        /*5.	The number of tickets for a particular concert must not exceed the location’s capacity where it will take place. */
        concertBookedTickets(concertValue) + 1 <= locationCapacity(concertLocation(concertValue))
    THEN
        concertBookedTickets(concertValue) := concertBookedTickets(concertValue) + 1
    END;
    
    
    
    
    
    /* Decrease booked tickets with 1 */
    decreaseConcertBookedTickets(concertValue) = 
    PRE
        concertValue : concerts &
        concertBookedTickets(concertValue) > 0
    THEN
        concertBookedTickets(concertValue) := concertBookedTickets(concertValue) - 1
    END;        





    /* Increase booked tickets with a number n */
    increaseConcertBookedTicketsWith(concertValue, ticketsNumberValue) = 
    PRE
        concertValue: concerts &
        ticketsNumberValue: NATURAL &
        /*5.	The number of tickets for a particular concert must not exceed the location’s capacity where it will take place. */
        concertBookedTickets(concertValue) + ticketsNumberValue <= locationCapacity(concertLocation(concertValue))
    THEN
        concertBookedTickets(concertValue) := concertBookedTickets(concertValue) + ticketsNumberValue
    END;
    
    
    
    
    
    /* Decrease booked tickets with a number n */
    decreaseConcertBookedTicketsWith(concertValue, ticketsNumberValue) = 
    PRE
        concertValue: concerts &
        ticketsNumberValue: NATURAL &
        ticketsNumberValue <= concertBookedTickets(concertValue)
    THEN
        concertBookedTickets(concertValue) := concertBookedTickets(concertValue) - ticketsNumberValue
    END;
   
    
    
    
    /* Get id */
    idValue <-- getConcertId(concertValue) = 
    PRE
        concertValue : concerts
    THEN
        idValue := concertId(concertValue)
    END;
    
      
      
      
    /* Get concert date and set concert date */
    dateValue <-- getConcertDate(concertValue) = 
    PRE
        concertValue : concerts
    THEN
        dateValue := concertDate(concertValue)
    END;
    
    setConcertDate(concertValue, dateValue) = 
    PRE
        concertValue : concerts &
        dateValue : STR &
        /* 2.	Multiple concerts can take place in the same location. However, the date of the concerts must not intersect each other. */
        ! con . (con : concerts & concertLocation(con) = concertLocation(concertValue) => concertDate(con) /= dateValue)   
    THEN
        concertDate(concertValue) := dateValue
    END;
        
    
    
    /* Get concert location and set concert location */
    locationValue <-- getLocationValue(concertValue) =
    PRE
        concertValue : concerts
    THEN
        locationValue := concertLocation(concertValue)
    END;
    
    setConcertLocation(concertValue, locationValue) =
    PRE
        concertValue : concerts &
        locationValue : locations &
        /*5.	The number of tickets for a particular concert must not exceed the location’s capacity where it will take place. */
        concertBookedTickets(concertValue) <= locationCapacity(locationValue) &
        /* 2.	Multiple concerts can take place in the same location. However, the date of the concerts must not intersect each other. */
        ! con . (con : concerts & concertLocation(con) = locationValue => concertDate(con) /= concertDate(concertValue))
    
    THEN
        concertLocation(concertValue) := locationValue
    END;
    
      
      
      
    /* Get booked tickets and set booked tickets */                    
    bookedTicketsValue <-- getConcertBookedTickets(concertValue) = 
    PRE
        concertValue : concerts 
    THEN
        bookedTicketsValue := concertBookedTickets(concertValue)
    END;
        
    setConcertBookedTickets(concertValue, bookedTicketValue) =
    PRE
        concertValue : concerts &
        bookedTicketValue : NATURAL &
        bookedTicketValue <= locationCapacity(concertLocation(concertValue))
    THEN
        concertBookedTickets(concertValue) := bookedTicketValue

    END

    
END
