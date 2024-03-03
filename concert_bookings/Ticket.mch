/* Ticket
 * Author: night
 * Creation date: 1/10/2024
 */
MACHINE
    Ticket
    
SEES
    String
    
USES
    Booking, Concert
    
SETS
    TICKET; TYPES = {simple, pro, ultimate}

CONSTANTS
    priceBasedOnTypes
    
PROPERTIES
    priceBasedOnTypes : TYPES --> NATURAL1 &
    priceBasedOnTypes = {simple |-> 50, pro |-> 150, ultimate |-> 350}
    
ABSTRACT_VARIABLES
    tickets,
    ticketId,
    ticketType,
    ticketPrice,
    ticketBooking
    
INVARIANT
    tickets <: TICKET &
    ticketId : tickets >-> NATURAL1 &
    ticketType : tickets --> TYPES &
    ticketPrice : tickets --> NATURAL1 &
    /* 1.	To each type of ticket the correspondent ticket price must be allocated. */
    ! tick . (tick : tickets => ticketPrice(tick) <= priceBasedOnTypes(ticketType(tick))) &
    ticketBooking : tickets --> bookings
    
INITIALISATION
    tickets,
    ticketId,
    ticketType,
    ticketPrice,
    ticketBooking := {}, {}, {}, {}, {}
    
OPERATIONS
    
    
    /* Create ticket */
    newTicket <-- createTicket(typeValue, priceValue, bookingValue) =
    PRE
        typeValue : TYPES &
        priceValue : NATURAL1 &
        bookingValue : bookings &
        /* 1.	To each type of ticket the correspondent ticket price must be allocated. */
        priceValue <= priceBasedOnTypes(typeValue)
    THEN
        ANY tick
        WHERE tick : TICKET - tickets
        THEN 
            tickets := tickets \/ {tick} ||
            ANY idValue
            WHERE idValue : NATURAL1 & idValue /: ran(ticketId)
            THEN
                ticketId(tick) := idValue
            END || 
            ticketBooking(tick) := bookingValue ||
            ticketType(tick) := typeValue ||
            ticketPrice(tick) := priceValue ||
            newTicket := tick
        END
    END;
    
    
    
    
    
    /* Remove ticket */
    removeTicket(ticketValue) = 
    PRE
        ticketValue : tickets
    THEN
        tickets := tickets - {ticketValue} ||
        ticketId := {ticketValue} <<| ticketId ||
        ticketType := {ticketValue} <<| ticketType ||
        ticketPrice := {ticketValue} <<| ticketPrice ||
        ticketBooking := {ticketValue} <<| ticketBooking
    END;  





    /* Remove all tickets from booking */
    removeAllTicketsFromBooking(bookingValue) = 
    PRE
        bookingValue: bookings
    THEN
        tickets := tickets - ticketBooking~[{bookingValue}] ||
        ticketBooking := ticketBooking |>> {bookingValue} ||
        ticketId := ticketBooking~[{bookingValue}] <<| ticketId ||
        ticketType := ticketBooking~[{bookingValue}] <<| ticketType ||
        ticketPrice := ticketBooking~[{bookingValue}] <<| ticketPrice
    END;
    
    
    
    /* Get id */
    idValue <-- getTicketId(ticketValue) = 
    PRE
        ticketValue : tickets
    THEN
        idValue := ticketId(ticketValue)
    END;
    
    
    
    
    /* Get price and set price */
    priceValue <-- getTicketPrice(ticketValue) = 
    PRE
        ticketValue : tickets
    THEN
        priceValue := ticketPrice(ticketValue)
    END;
    
    setTicketPrice(ticketValue, priceValue) = 
    PRE
        ticketValue: tickets &
        priceValue : NATURAL1 &
        /* 1.	To each type of ticket the correspondent ticket price must be allocated. */
        priceValue <= priceBasedOnTypes(ticketType(ticketValue))
    THEN
        ticketPrice(ticketValue) := priceValue
    END;   

       
       
       
    /* Get type and set type */
    typeValue <-- getTicketType(ticketValue) = 
    PRE
        ticketValue : tickets
    THEN
        typeValue := ticketType(ticketValue)
    END;
    
    setTicketType(ticketValue, typeValue) = 
    PRE
        ticketValue : tickets &
        typeValue : TYPES &
        /* 1.	To each type of ticket the correspondent ticket price must be allocated. */
        ticketPrice(ticketValue) <= priceBasedOnTypes(typeValue)
    THEN
        ticketType(ticketValue) := typeValue
    END;
    
    
    
    
    /* Get Booking and set Booking */
    bookingValue <-- getTicketBooking(ticketValue) = 
    PRE
        ticketValue : tickets
    THEN
        bookingValue := ticketBooking(ticketValue)
    END;
    
    setTicketBooking(ticketValue, bookingValue) = 
    PRE
        ticketValue: tickets &
        bookingValue : bookings
    THEN
        ticketBooking(ticketValue) := bookingValue
    END
   

END
