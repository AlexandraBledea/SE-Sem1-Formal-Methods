/* Participant
 * Author: night
 * Creation date: 1/10/2024
 */
MACHINE
    Participant

SEES
    String

SETS
    PARTICIPANT
    
ABSTRACT_VARIABLES
    participants,
    participantId,
    participantName,
    participantAge,
    participantUsername,
    participantEmail,
    participantPhoneNumber,
    participantAddress

INVARIANT
    participants <: PARTICIPANT &
    participantId: participants >-> NATURAL1 &
    participantName: participants --> STR &
    participantAge: participants --> NATURAL1 &
    participantUsername: participants >-> STR &
    participantEmail: participants >-> STR &
    participantPhoneNumber: participants >-> STR &
    participantAddress: participants --> STR
    
INITIALISATION
    participants,
    participantId,
    participantName,
    participantAge,
    participantUsername,
    participantEmail,
    participantPhoneNumber,
    participantAddress := {}, {}, {}, {}, {}, {}, {}, {}
    
OPERATIONS
    
    
    /* Create participant */
    newParticipant <-- createParticipant(nameValue, ageValue, usernameValue, emailValue, phoneNumberValue, addressValue) =
    PRE
        nameValue : STR &
        ageValue : NATURAL1 &
        usernameValue : STR &
        usernameValue /: ran(participantUsername) &
        emailValue : STR &
        emailValue /: ran(participantEmail) &
        phoneNumberValue : STR & 
        phoneNumberValue /: ran(participantPhoneNumber) &
        addressValue : STR
    THEN
        ANY part
        WHERE part : PARTICIPANT - participants
        THEN
            participants := participants \/ {part} ||
            ANY idValue
            WHERE idValue : NATURAL1 & idValue /: ran(participantId)
            THEN
                participantId(part) := idValue
            END ||
            participantName(part) := nameValue ||
            participantAge(part) := ageValue ||
            participantUsername(part) := usernameValue ||
            participantEmail(part) := emailValue ||
            participantPhoneNumber(part) := phoneNumberValue ||
            participantAddress(part) := addressValue ||
            newParticipant := part
        END
    END;
    
    
            
    
    
   /* Remove participant */
   removeParticipant(participantValue) =
   PRE
       participantValue : participants
   THEN
       participants := participants - {participantValue} ||
       participantId := {participantValue} <<| participantId ||
       participantName := {participantValue} <<| participantName ||
       participantUsername := {participantValue} <<| participantUsername ||
       participantEmail := {participantValue} <<| participantEmail ||
       participantPhoneNumber := {participantValue} <<| participantPhoneNumber ||
       participantAddress := {participantValue} <<| participantAddress ||
       participantAge := {participantValue} <<| participantAge
   END;
    
    
  
  
  
    /* Get id */
    idValue <-- getParticipantId(participantValue) =
    PRE
        participantValue : participants
    THEN
        idValue := participantId(participantValue)
    END;
    
    
    
    
    
    /* Get name and set name */
    nameValue <-- getParticipantName(participantValue) = 
    PRE
        participantValue : participants
    THEN
        nameValue := participantName(participantValue)
    END;
    
    setParticipantName(participantValue, nameValue) = 
    PRE
        participantValue : participants &
        nameValue : STR
    THEN
        participantName(participantValue) := nameValue
    END;
    
    
    
    
    
    /* Get age and set age */
    ageValue <-- getParticipantAge(participantValue) = 
    PRE
        participantValue : participants 
    THEN
        ageValue := participantAge(participantValue)
    END;
    
    setParticipantAge(participantValue, ageValue) = 
    PRE
        participantValue : participants &
        ageValue : NATURAL1
    THEN
        participantAge(participantValue) := ageValue
    END;
    
    
    
    
    
    /* Get email and set email */
    emailValue <-- getParticipantEmail(participantValue) =
    PRE
        participantValue : participants
    THEN
        emailValue := participantEmail(participantValue)
    END;
    
    setParticipantEmail(participantValue, emailValue) = 
    PRE
        participantValue : participants &
        emailValue : STR &
        emailValue /: ran(participantEmail)
    THEN
        participantEmail(participantValue) := emailValue
    END;
    
    
    
    
    /* Get phone number and set phone number */
    phoneNumberValue <-- getParticipantPhoneNumber(participantValue) =
    PRE
        participantValue : participants
    THEN
        phoneNumberValue := participantPhoneNumber(participantValue)
    END;
    
    setParticipantPhoneNumber(participantValue, phoneNumberValue) = 
    PRE
        participantValue : participants &
        phoneNumberValue : STR &
        phoneNumberValue /: ran(participantPhoneNumber)
    THEN
        participantPhoneNumber(participantValue) := phoneNumberValue
    END;
    
    
    
    
    /* Get username and set username */
    usernameValue <-- getParticipantUsername(participantValue) = 
    PRE
        participantValue: participants
    THEN
        usernameValue := participantUsername(participantValue)
    END;
    
    setParticipantUsername(participantValue, usernameValue) = 
    PRE
        participantValue : participants &
        usernameValue : STR &
        usernameValue /: ran(participantUsername)
    THEN
        participantUsername(participantValue) := usernameValue
    END;
    
    
    
    /* Get address and set address */
    addressValue <-- getParticipantAddress(participantValue) = 
    PRE
        participantValue : participants
    THEN
        addressValue := participantAddress(participantValue)
    END;
    
    setParticipantAddress(participantValue, addressValue) = 
    PRE
        participantValue : participants &
        addressValue: STR
    THEN
        participantAddress(participantValue) := addressValue
    END
   
    
END
