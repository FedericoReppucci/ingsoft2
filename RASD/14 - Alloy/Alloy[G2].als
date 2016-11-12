//ALLOY MODEL FOR GOALS [G2.0], [G2.1] AND RELATIVE REQUIREMENTS

//-----------------------THE WORLD ------------------------------------------------------

sig User{
	//goal-related user relations
	userIsAt : one Location,
	canFind : set Car,
	specifiedAddress : lone Address,

	//requirements-related user relations
	accesses : one PowerEnJoyApp,
	uses : set Function
}{
	//a user can find cars only using the app ( in the sense of finding as stated by the goal )
	some canFind iff ReserveACar in uses

	//a user specifies an address only in the contest of the ReserveACar functionality ( in thi context )
	one specifiedAddress implies ReserveACar in uses
}

//only the addresses specified by a user are shown in this model
fact relevantAddress{ no a : Address | no u : User | a in u.specifiedAddress}

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

//properties of  a range
fact RangeIsReflexive{ all l : Location | l in l.inRange }
fact RangeIsSymmetric{ all l1,l2 : Location | l2 in l1.inRange implies l1 in l2.inRange }

//	[G2.0]: The user is able to find the location of all available cars within a certain range from their current location.
//	[G2.1]: The user is able to find the location of all available cars within a certain range from a specified address.

assert G2 { all u : User, c : AvailableCar | 
					ReserveACar in u.uses and
					(c.carIsAt in u.userIsAt.inRange and no u.specifiedAddress) or 
					(one u.specifiedAddress and c.carIsAt in u.specifiedAddress.isAt.inRange) iff c in u.canFind } 

//--------------------- THE MACHINE --------------------------------------------------------------

one sig PowerEnJoyApp{
	has : set Function 
}{
	//the app has every one of its functions
	all f : Function | f in has
}
//[R2.1]: The "Reserve a car" function can be accessed by the user from the home page of the app
fact userCanAccessAllFunctions{ all u : User | u.uses in u.accesses.has}

//[R2.2]: The "Reserve a car" function allows the user to select a range : in this model we assume the range 
//			   considered to be the range of choice
//[R2.3]: The system acquires the user's current position through the GPS coordinates of the user's phone
fact userCoordinatesAcquired{ all u : User | ReserveACar in u.uses iff ( one r : ReserveACar | u in 
	r.acquiresUser/*GPS*/.signalsForUser ) }

abstract sig Function{}
one sig ReserveACar extends Function{
		acquiresCars : set GPSCar,
		acquiresUser : one GPSUser,
		acquiresAddress : lone GPSAddress
}{
	acquiresAddress.signalsForAddress =  acquiresUser.signalsForUser.specifiedAddress 

	//[R2.4]: The system tracks all available cars' current position through their GPS coordinates
	acquiresCars.signalsForCar = AvailableCar

	//[R2.5]: The "Reserve a car" function allows the user to select a starting position for the search, which can 
	//			  be either their current location or a given address
	no acquiresAddress and (all c : Car | c in acquiresUser.signalsForUser.canFind iff 
		c.carIsAt.inRange = acquiresUser.signalsForUser.userIsAt.inRange ) or
	one acquiresAddress and ( all c : Car | c in acquiresUser.signalsForUser.canFind iff 
		c.carIsAt.inRange = acquiresAddress.signalsForAddress.isAt.inRange )
}

//[R2.6]: When the user confirms the inserted parameters the search is carried out and the "Reserve a car" 
//				function displays to the user
// the data of the search acquired from the system in a Google provided map : this model shows the instant 
//after confirmation

//this fact states that GPS coordinates are in general different for different objects 
fact uniqueGPS{ (all g1, g2 : GPSCar | g1 != g2 iff g1.signalsForCar != g2.signalsForCar) and
							(all g1, g2 : GPSUser | g1 != g2 iff g1.signalsForUser != g2.signalsForUser) and
							(all g1, g2 : GPSAddress | g1 != g2 iff g1.signalsForAddress != g2.signalsForAddress)}

// this fact conveys the meaning of "the user can find only the cars tracked via GPS by the system"
fact canFindAcquiredCarsOnly{ all r : ReserveACar | 
	r.acquiresCars.signalsForCar = r.acquiresUser.signalsForUser.canFind }

abstract sig GPS{}
sig GPSCar extends GPS{
	signals : one Location,
	signalsForCar : one Car
}{
	//GPS coordinates exist in the model as long as a "ReserveACar" functionality tracks them
	one signalsForCar iff ( one r : ReserveACar | this in r.acquiresCars ) 
}
sig GPSAddress{
	signals : one Location,
	signalsForAddress : one Address
}{
	//GPS coordinates exist in the model as long as a "ReserveACar" functionality tracks them
	one signalsForAddress iff ( one r : ReserveACar | this = r.acquiresAddress )
}
sig GPSUser{
	signals : one Location,
	signalsForUser : one User
}{
	one signalsForUser iff one signalsForUser.uses

	//GPS coordinates exist in the model as long as a "ReserveACar" functionality tracks them
	one signalsForUser iff ( one r : ReserveACar | this = r.acquiresUser )   
}


//[D3.0]: The GPS coordinates of the cars received by the system always correspond to 
//			  the actual positions of the cars.
//[D3.1]: The GPS coordinates of a user received by the system always correspond to 
//			  the actual position of the user.

fact GPSUserCorrect{ all g : GPSUser | g.signals = g.signalsForUser.userIsAt}
fact GPSCarCorrect{ all g : GPSCar | g.signals = g.signalsForCar.carIsAt}
fact GPSUserCorrect{ all g : GPSAddress | g.signals = g.signalsForAddress.isAt}

check G2 for 4


