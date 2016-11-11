/*
	[G2.0]: The user is able to find the location of all available cars within a certain range from
	 their current location.
	[G2.1]: The user is able to find the location of all available cars within a certain range from 
	a specified address.
	[G3.0]: The user is able to pick a car among the available ones and reserve it.
	[G3.1]: A reserved car is not available for renting until one hour has passed from 
	the moment a user reserved it.
	[G3.2] A car becomes available again after one hour has passed from its reservation and it
 	is parked in a safe area less than 3 km away from a power grid having more than 20% of its
	battery
	[G4]: The user pays 1 EUR if he/she doesn't reach the car he/she rent within 1 hour from the reservation.
	[G5]: The user is able to unlock and open the car he/she rent when he/she is nearby the car

	[G6.0]: From the moment of ignition, the user is charged for a constant amount of money per minute
	[G6.1]: The user is notified of the current charges through a screen on the car.
	[G7.0]: The charging of the user stops as soon as the driver parks the car in a safe area and exits from it.
	[G7.1]: The car is automatically locked as soon as the driver parks the car in a safe area and exits from it. 
	[G8]: A discount of 10% is applied on the last ride if the driver took at least two  passengers onto the 
	car and no higher discount or any extra fee can be applied.
	[G9]: If a car is left with more than 50% of its maximum battery available, a discount of 20% is applied 
	on the last ride and no higher discount or any extra fee can be applied.
	[G10]: A discount of 30% is applied on the last ride if a car is left at special parking areas where they 
	can be recharged and the driver takes care of  plugging the car into the power grid and no higher discount or any extra fee can be applied.

*/

//-------------------------- G2

//--------------------- THE MACHINE --------------------

one sig PowerEnJoyApp{
	has : set Function 
}{
	all f : Function | f in has
}
//contains [R2.1]
fact canAccessAllFunctions{ all u : User | u.uses in u.accesses.has}

abstract sig Function{}
one sig ReserveACar extends Function{
		user : one User,
		acquiresCars : set GPS,
		acquiresUser : one GPS,
		acquiresAddress : lone GPS,
}{

	user.userIsAt = acquiresUser.signals
	this in user.uses
	//range restrictions 
	acquiresCars.signalsFor in ( Car :> acquiresCars.signalsFor)
	acquiresUser.signalsFor in ( User :> acquiresUser.signalsFor)
	acquiresAddress.signalsFor in ( Address :> acquiresAddress.signalsFor)

	//acquires cars in range of a user
	(no acquiresAddress and acquiresCars.signals in acquiresUser.signals.inRange) or 
	(one acquiresAddress and acquiresCars.signals in acquiresAddress.signals.inRange )
	
	//the app finds all the cars in range of the user or address
	all c : Car, g : GPS | (no acquiresAddress and g.signals in acquiresUser.signals.inRange  and g.signalsFor = c ) iff c in acquiresCars.signalsFor
	all c : Car, g : GPS | (one acquiresAddress and g.signals in acquiresAddress.signals.inRange  and g.signalsFor = c ) iff c in acquiresCars.signalsFor

	//for all cars in acquiresCars User | acquiresUser.signalsFor is User, User can find acquiresCars.signalsFor
	acquiresCars.signalsFor = acquiresUser.signalsFor.canFind
}

//   for all C,L if L | C is in L => C in acquireCars.signals iff L in range L ' 

sig GPS{
	signals : one Location,
	signalsFor : one (User + Car + Address)
}

fact a{all g : GPS, r : ReserveACar | g in r.acquiresCars + r.acquiresUser + r.acquiresAddress }

//[D3]
fact GPSIsCorrect{ all g: GPS | g.signals = g.signalsFor.userIsAt  or  g.signals = g.signalsFor.carIsAt or g.signals = g.signalsFor.isAt  }

//can use and acquires c <=> canFind c


//-----------------------THE WORLD --------------------
sig User{
	//goal-related user relations
	userIsAt : one Location,
	canFind : set Car,
	specifiedAddress : lone Address,

	//requirements-related user relations
	accesses : one PowerEnJoyApp,
	uses : set Function
}{
	some canFind iff ReserveACar in uses
	one specifiedAddress iff ReserveACar in uses
}

sig Car{
	carIsAt : one Location,
}
sig AvailableCar in Car{}

sig Location{
	inRange : set Location
}

sig Address{
	isAt : one Location
}

fact RangeIsReflexive{ all l : Location | l in l.inRange }
fact RangeIsSymmetric{ all l1,l2 : Location | l2 in l1.inRange implies l1 in l2.inRange }


assert G2 { all u : User, c : Car | 
					ReserveACar in u.uses and
					(c.carIsAt in u.userIsAt.inRange and no u.specifiedAddress) or (c.carIsAt in u.specifiedAddress.isAt) iff c in u.canFind } 
check G2 for 2 but 1 User 

pred p{one u: User | #u.canFind > 0}
run p for 2 but 2 User

