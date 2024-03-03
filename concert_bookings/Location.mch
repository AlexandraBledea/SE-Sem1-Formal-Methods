/* Location
 * Author: night
 * Creation date: 1/10/2024
 */
MACHINE
    Location
    
SEES
    String
    
SETS
    LOCATION
    
ABSTRACT_VARIABLES
    locations,
    locationId,
    locationName,
    locationCapacity
    
INVARIANT
    locations <: LOCATION &
    locationId : locations >-> NATURAL1 &
    locationName : locations --> STR &
    locationCapacity : locations --> NATURAL

INITIALISATION
    locations,
    locationId,
    locationName,
    locationCapacity := {}, {}, {}, {}
    
OPERATIONS
    
    /* Create location */
    newLocation <-- createLocation(nameValue, capacityValue) =
    PRE
        nameValue : STR &
        capacityValue : NATURAL
    THEN
        ANY loc
        WHERE loc : LOCATION - locations
        THEN 
            locations := locations \/ {loc} ||
            ANY idValue
            WHERE idValue : NATURAL1 & idValue /: ran(locationId)
            THEN
                locationId(loc) := idValue
            END ||
            locationName(loc) := nameValue ||
            locationCapacity(loc) := capacityValue ||
            newLocation := loc
        END
    END;
    
    
    
          
    
    /* Remove location */
    removeLocation(locationValue) = 
    PRE
        locationValue: locations
    THEN
        locations := locations - {locationValue} ||
        locationId := {locationValue} <<| locationId ||
        locationName := {locationValue} <<| locationName ||
        locationCapacity := {locationValue} <<| locationCapacity
    END;
    
       
    
    
    
    /* Get id */
    idValue <-- getLocationId(locationValue) =
    PRE
        locationValue : locations
    THEN
        idValue := locationId(locationValue)
    END;
    
    
    
    
    
    /* Get name and set name */
    nameValue <-- getLocationName(locationValue) = 
    PRE
        locationValue : locations
    THEN
        nameValue := locationName(locationValue)
    END;
    
    setLocationName(locationValue, nameValue) = 
    PRE
        locationValue: locations &
        nameValue : STR
    THEN
        locationName(locationValue) := nameValue
    END;
    
    
    
    
    
    /* Get capacity and set capacity */
    capacityValue <-- getLocationCapacity(locationValue) = 
    PRE
        locationValue : locations
    THEN
        capacityValue := locationCapacity(locationValue)
    END;
    
    setLocationCapacity(locationValue, capacityValue) =
    PRE
        locationValue : locations &
        capacityValue : NATURAL 
    THEN
        locationCapacity(locationValue) := capacityValue
    END
    
    
END
