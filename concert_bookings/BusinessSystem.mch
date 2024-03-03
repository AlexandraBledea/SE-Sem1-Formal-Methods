/* BusinessSystem
 * Author: night
 * Creation date: 1/14/2024
 */
MACHINE
    BusinessSystem
SEES
    String
    
INCLUDES Concert, Booking, Ticket, Location, Participant
    
PROMOTES
increaseBookingTicketsNumberWith, decreaseBookingTicketsNumberWith, decreaseConcertBookedTicketsWith, increaseConcertBookedTicketsWith, removeLocation, removeAllConcertsFromLocation, removeBooking, removeAllTicketsFromBooking

OPERATIONS
       
    increaseTicketsForBooking(bookingValue, ticketsNumber) = 
    PRE
        bookingValue : bookings &
        ticketsNumber: NATURAL &
        bookingTicketsNumber(bookingValue) + ticketsNumber <= 10 &
        concertBookedTickets(bookingConcert(bookingValue)) + ticketsNumber <= locationCapacity(concertLocation(bookingConcert(bookingValue)))
    THEN
        increaseBookingTicketsNumberWith(bookingValue, ticketsNumber) ||
        increaseConcertBookedTicketsWith(bookingConcert(bookingValue), ticketsNumber)
    END;
    
    
    decreaseTicketsForBooking(bookingValue, ticketsNumber) =
    PRE
        bookingValue: bookings &
        ticketsNumber: NATURAL &
        ticketsNumber <= bookingTicketsNumber(bookingValue) & 
        ticketsNumber <= concertBookedTickets(bookingConcert(bookingValue))
    THEN
        decreaseBookingTicketsNumberWith(bookingValue, ticketsNumber) ||
        decreaseConcertBookedTicketsWith(bookingConcert(bookingValue), ticketsNumber)
    END;
    
    
    deleteLocation(locationValue) = 
    PRE
        locationValue: locations
    THEN
        removeLocation(locationValue) ||
        removeAllConcertsFromLocation(locationValue)
    END;
    
    deleteBooking(bookingValue) = 
    PRE
        bookingValue: bookings
    THEN
        removeBooking(bookingValue) ||
        removeAllTicketsFromBooking(bookingValue)
    END
    
       
END
