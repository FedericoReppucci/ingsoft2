
	//[G6.0]: From the moment of ignition, the user is charged for a constant amount of money per minute
	//[G6.1]: The [user] driver is notified of the current charges through a screen on the car.
	//[G7.0]: The charging of the user stops as soon as the driver parks the car in a safe area and exits from it.
	//[G7.1]: The car is automatically locked as soon as the driver parks the car in a safe area and exits from it. 
	
	//[D7.1]: If the sensors in the car detect no one inside, there are no people in the car 

//ALLOY MODEL FOR GOALS *** AND RELATIVE REQUIREMENTS

//-----------------------THE WORLD --------------------------------------------------------------------------------------

sig Person{}

sig User in Person{
	isChargedFor : lone Car,

}

sig Driver in Person{
	isNotified : set ConstantCharge,
	isDriving : lone Car,
	hasParked : lone Car
}{
	//a driver is driving if and only if has not parked a car
	one isDriving iff no hasParked
	//a driven car is ignited
	isDriving  in IgnitedCar
	//a parked car is stopped
	hasParked  in StoppedCar
}

sig ConstantCharge{}

abstract sig Car{
	hasIn : set Person,
	detects : set Sensor
}{
	// a sensor is detected if and only if is in this car 
	all s : Sensor | s in detects iff this in s.isIn
}

sig Sensor{
	detectedPerson : one Person,
	isIn : one Car
}

sig IgnitedCar extends Car{
	displays : set ConstantCharge
}

sig StoppedCar extends Car{
	parkedIn : one Area
}
 
sig LockedCar in Car{}{
	this not in UnlockedCar
}
sig UnlockedCar in Car{}{
	this not in LockedCar{}
}

fact{ LockedCar + UnlockedCar = Car}

abstract sig Area{}
sig SafeArea extends Area{}

//no person can be in two cars at the same time
fact{ all c1, c2 : Car | c1 != c2 implies (no p : Person | p in c1.hasIn and p in c2.hasIn ) }

//a driver must be in a car to drive it
fact{ all d : Driver, c : Car | c in d.isDriving implies d in c.hasIn }

//no two sensor detect the same person
fact{ all s1, s2 : Sensor | s1 !=  s2 iff ( no p : Person | p in s1.detectedPerson and p in s2.detectedPerson ) }

//a sensor can only detect a person inside the car 
fact{ all c : Car | c.detects.detectedPerson in c.hasIn }

//if someone has parked a car, that car is parked somewhere
fact{ all c : StoppedCar, d : Driver | c in d.hasParked implies one c.parkedIn }

//a parked car has been parked by only one person
fact{ all d1, d2 : Driver | d1 != d2 implies ( no c : Car | c in d1.hasParked and c in d2.hasParked ) }

//only the safe areas with some car parked in them are considered in the model
fact{ all sa : SafeArea | one c : Car | sa in c.parkedIn }

//all ignited cars have a driver
fact{ all c : IgnitedCar | one d : Driver | c in d.isDriving}

//all constant charges considered in the model are displayed by some car
fact{ all ch : ConstantCharge | one c : Car | ch in c.displays}

//a driver is notified of what the car he is driving displays
fact{ all d : Driver | d.isNotified = d.isDriving.displays }

//for the sake of simplicity,  no driver who has parked a car can be in another car
fact{ no c1, c2 : Car | ( one d : Driver | d in c1.hasIn and c2 in d.hasParked ) }

//[D7.1]: If the sensors in the car detect no one inside, there are no people in the car 
// in this model we consider the weakest possible sensor accuracy which still allows to satisfy the goal, in the form of D7.1
fact sensorAccuracy{ all c : Car | no c.detects iff no c.hasIn }

assert G6_0 {  all c : Car | c in IgnitedCar iff ( one u : User | c in u.isChargedFor)}
assert G6_1 { all d : Driver | some d.isNotified iff ( one c : Car, u : User | c in u.isChargedFor and c in d.isDriving) }	
/*see goal interpretation for [G7.0]*/
assert G7 { all u : User, c : Car | c.parkedIn in SafeArea and ( no c.hasIn ) implies ( c not in u.isChargedFor and c in LockedCar ) }

check G6_0

check G6_1

check G7

pred p{}
run p for 6

//--------------------- THE MACHINE ----------------------------------------------------------------------------------------------------------

one sig System{
	lastReservation : set User -> one Car
}

//[R6.1]: When a car is ignited the system starts charging the last user who reserved the car
fact{ all u : User, s : System | one u.isChargedFor iff (one c : Car | s -> u -> c in lastReservation and c in u.isChargedFor)}
fact{ all c : Car, s : System, u : User | ( c in IgnitedCar and ( s -> u -> c in lastReservation ) implies c in u.isChargedFor ) }

// a car can be ignited only if a user had reserved it
fact{ all c : Car, s : System |  c in IgnitedCar iff ( one u : User | s -> u -> c in lastReservation )}

//a car displays charges if ignited
fact{ all c : Car | c in IgnitedCar  implies some c.displays} 

// in the system each user has only one "last reservation"
fact{ all c : Car, s : System | lone u : User | s -> u -> c in lastReservation }

//[R6.2]: When the charging starts, the display on the car shows a "Current charge" field 
//with a number representing the current total charge, which starts from 0
fact{ all u : User | one u.isChargedFor iff ( one c : Car | c in u.isChargedFor and some c.displays ) }


//[R6.3]: Once a minute the "Current charge" value is incremented by a set amount : this requirement is not modeled in this model

//[R7.1]: When a car is stopped and the sensors in the car detect no one inside,
// if a user was being charged for the car the system stops charging him/her. 
//[R7.2]: One minute after a car has been stopped and the sensors in the car detect no one inside, the system locks the car
fact{ all c : StoppedCar | no c.hasIn iff ( no u : User | c in u.isChargedFor ) and c in LockedCar }
