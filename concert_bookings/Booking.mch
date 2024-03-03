/* Booking
 * Author: night
 * Creation date: 1/10/2024
 */
MACHINE
    Booking
    
SEES 
    String
    
USES
    Participant, Concert, Location
    
SETS 
    BOOKING
    
ABSTRACT_VARIABLES
    bookings,
    bookingId,
    bookingTicketsNumber,
    bookingConcert,
    bookingParticipant
    
INVARIANT
    bookings <: BOOKING &
    bookingId : bookings >-> NATURAL1 &
    bookingTicketsNumber : bookings --> NATURAL &
    /* 4.	A participant can make a booking for maximum 10 tickets.  */
    ! bo . (bo: bookings => bookingTicketsNumber(bo) <= 10) &
    bookingConcert: bookings --> concerts &
    bookingParticipant : bookings --> participants    
    
    
      /* 3.	A participant can have multiple bookings. However, a participant must not have multiple bookings for the same concert. */
//    ! (bo1 , bo2) . ((bo1 : bookings & bo2 : bookings & bookingParticipant(bo1) = bookingParticipant(bo2)) => bookingConcert(bo1) /= bookingConcert(bo2))


    
INITIALISATION
    bookings,
    bookingId,
    bookingConcert,
    bookingParticipant,
    bookingTicketsNumber := {}, {}, {}, {}, {}

OPERATIONS
    
    
    
    
    /* Create Booking */
    newBooking <-- createBooking(concertValue, participantValue) =
    PRE
        concertValue : concerts &
        participantValue : participants &
        /* 3.	A participant can have multiple bookings. However, a participant must not have multiple bookings for the same concert. */
        ! bo . ( bo : bookings & bookingConcert(bo) = concertValue => bookingParticipant(bo) /= participantValue )
        
    THEN
        ANY bo
        WHERE bo : BOOKING - bookings
        THEN bookings := bookings \/ {bo} ||
            ANY idValue
            WHERE idValue : NATURAL1 & idValue /: ran(bookingId)
            THEN bookingId(bo) := idValue
            END ||
            bookingConcert(bo) := concertValue ||
            bookingParticipant(bo) := participantValue ||
            bookingTicketsNumber(bo) := 0 ||
            newBooking := bo
        END
    END;
    
    
    
    
    
    /* Remove Booking */   
    removeBooking(bookingValue) = 
    PRE
        bookingValue : bookings
    THEN
        bookings := bookings - {bookingValue} ||
        bookingId := {bookingValue} <<| bookingId ||
        bookingConcert := {bookingValue} <<| bookingConcert ||
        bookingParticipant := {bookingValue} <<| bookingParticipant ||
        bookingTicketsNumber := {bookingValue} <<| bookingTicketsNumber
    END;
    
    
    
    
    
    /* Remove all bookings from participant */
    removeAllBookingsFromParticipant(participantValue) = 
    PRE
        participantValue : participants
    THEN
        bookings := bookings - bookingParticipant~[{participantValue}] ||
        bookingParticipant := bookingParticipant |>> {participantValue} ||
        bookingId := bookingParticipant~[{participantValue}] <<| bookingId ||
        bookingTicketsNumber := bookingParticipant~[{participantValue}] <<| bookingTicketsNumber ||
        bookingConcert := bookingParticipant~[{participantValue}] <<| bookingConcert
    END;
    
    
    
    
    
    /* Remove all bookings from concert */
    removeAllBookingsFromConcert(concertValue) = 
    PRE
        concertValue : concerts
    THEN
        bookings := bookings - bookingConcert~[{concertValue}] ||
        bookingConcert := bookingConcert |>> {concertValue} ||
        bookingId := bookingConcert~[{concertValue}] <<| bookingId ||
        bookingTicketsNumber := bookingConcert~[{concertValue}] <<| bookingTicketsNumber ||
        bookingParticipant := bookingConcert~[{concertValue}] <<| bookingParticipant
    END;
    
    
    
        
    
     
    /* Increase booking tickets with 1*/
    increaseBookingTicketsNumber(bookingValue) =
    PRE
        bookingValue : bookings &
        /* 4.	A participant can make a booking for maximum 10 tickets.  */
        bookingTicketsNumber(bookingValue) + 1 <= 10
    THEN
        bookingTicketsNumber(bookingValue) := bookingTicketsNumber(bookingValue) + 1
    END;
    
    
    
    
    
    /* Decrease booking tickets with 1 */
    decreaseBookingTicketsNumber(bookingValue) =
    PRE
        bookingValue : bookings &
        bookingTicketsNumber(bookingValue) > 0
    THEN
        bookingTicketsNumber(bookingValue) := bookingTicketsNumber(bookingValue) - 1
    END;
    
    
    
    
    
    /* Increase booking tickets with a number n */
    increaseBookingTicketsNumberWith(bookingValue, ticketsNumberValue) = 
    PRE
        bookingValue: bookings &
        ticketsNumberValue: NATURAL &
        /* 4.	A participant can make a booking for maximum 10 tickets.  */
        bookingTicketsNumber(bookingValue) + ticketsNumberValue <= 10
    THEN
        bookingTicketsNumber(bookingValue) := bookingTicketsNumber(bookingValue) + ticketsNumberValue
    END;
        
        
        
        
        
    /* Decrease booking tickets with a number n*/    
    decreaseBookingTicketsNumberWith(bookingValue, ticketsNumberValue) = 
    PRE
        bookingValue: bookings &
        ticketsNumberValue: NATURAL &
        ticketsNumberValue <= bookingTicketsNumber(bookingValue)
    THEN
        bookingTicketsNumber(bookingValue) := bookingTicketsNumber(bookingValue) - ticketsNumberValue
    END;
    
    
    
    
             
    /* Get id */
    idValue <-- getBookingId(bookingValue) =
    PRE
        bookingValue : bookings
    THEN
        idValue := bookingId(bookingValue)
    END;
    
    
    
    
    
    /* Get concert and set concert */
    concertValue <-- getBookingConcert(bookingValue) = 
    PRE
        bookingValue : bookings
    THEN
        concertValue := bookingConcert(bookingValue)
    END;
    
      
    setBookingConcert(bookingValue, concertValue) = 
    PRE
        bookingValue : bookings &
        concertValue : concerts &
        /* 3.	A participant can have multiple bookings. However, a participant must not have multiple bookings for the same concert. */
        ! bo . (bo: bookings & bookingConcert(bo) = concertValue => bookingParticipant(bo) /= bookingParticipant(bookingValue))
    THEN
        bookingConcert(bookingValue) := concertValue
    END;
    
    
    
    
    
    /* Get participant and set participant */
    participantValue <-- getBookingParticipant(bookingValue) = 
    PRE
        bookingValue : bookings
    THEN
        participantValue := bookingParticipant(bookingValue)
    END;
    
    
    setBookingParticipant(bookingValue, participantValue) = 
    PRE
        bookingValue : bookings &
        participantValue : participants &
        /* 3.	A participant can have multiple bookings. However, a participant must not have multiple bookings for the same concert. */
        ! bo . (bo: bookings & bookingParticipant(bo) = participantValue => bookingConcert(bo) /= bookingConcert(bookingValue))      
    THEN
        bookingParticipant(bookingValue) := participantValue
    END;
    
    
    
    
    
    
    /* Get tickets number and set tickets number */
    ticketsNumberValue <-- getBookingTicketsNumber(bookingValue) = 
    PRE
        bookingValue : bookings
    THEN
        ticketsNumberValue := bookingTicketsNumber(bookingValue)
    END;
    
    setBookingTicketsNumber(bookingValue, ticketsNumberValue) = 
    PRE
        bookingValue : bookings &
        ticketsNumberValue : NATURAL &
        /* 4.	A participant can make a booking for maximum 10 tickets.  */
        ticketsNumberValue <= 10
    THEN
        bookingTicketsNumber(bookingValue) := ticketsNumberValue
    END


END
