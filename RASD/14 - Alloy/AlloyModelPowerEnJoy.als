//-------------- PowerEnJoy -------  RASD ----- ALLOY MODEL

//areas of the city divided into safe and non-safe areas
sig CityArea{}
sig SafeArea, NonSafeArea extends CityArea{}
sig SpecialSafeArea extends SafeArea{}

//a power grid station where cars can be plugged in
sig PowerGrid{}

//notification received by an employee
sig RetrievalRequest{
	carToRetrieve : one Car
}{
	carToRetrieve.state in Dislocated
}

//created by a user to reserve a car
sig Reservation{
	status : one ReservationStatus,
	wasUsed : one UsedState,
	reservedCar : one Car,
	reservingUser : one User
}{
	status in Active => reservedCar.state in (Reserved + Unavailable + InUse)
	status in Active  => reservingUser.id.status in Valid && reservingUser.paymentInfo.status in Valid
	status in  Active => #reservingUser.pendingPayment = 0 
	// a reservation can be active if and only if is active for some user
	status in Active <=> ( some u : User | this = u.activeReservation )
}

abstract sig UsedState{}
sig Used,Unused extends UsedState{}

abstract sig ReservationStatus{}
sig Active, Inactive extends ReservationStatus{}

//a car has a state, a current position, can have a driver, passengers, and can be plugged  in a power grid
sig Car{
	state : one CarState,
	engine : one EngineState,
	battery: one BatteryState,
	position : one CityArea,
	driver : lone Person,
	passengers : set Person,
	plugged : lone PowerGrid
}{
	//state specification for a car

	state in Available => position in SafeArea && ( no r : Reservation | r.reservedCar = this && r.status in Active ) 
										&& engine in Off && battery not in LT20

	state in Dislocated => position in NonSafeArea && ( no r : Reservation | r.reservedCar = this && r.status in Active ) && engine in Off

	state in Reserved => position in SafeArea && ( one r : Reservation | r.reservedCar = this && r.status in Active  && r.wasUsed in Unused )
										 && engine in Off && battery not in LT20

	state in Unavailable => ( one r : Reservation | r.reservedCar = this && r.status in Active && r.wasUsed in Used )   && engine in Off

	state in InUse <=> engine in On

	//if and only if the engine is on, the car has a driver ( the moment when the driver enters the car and the engine is still off is not modeled ) and can have passengers
	engine in On <=> #driver > 0
	#passengers > 0 => engine in On
	
	//a car can be plugged in if and only if the engine is off
	#plugged > 0 <=> engine in Off && position in SpecialSafeArea
}

abstract sig CarState {}
sig Available, Reserved, Dislocated, Unavailable, InUse extends CarState{}

abstract sig EngineState{}
sig On,Off extends EngineState{}

abstract sig BatteryState{}
sig LT20, LT50, MT50 extends BatteryState{}

//status of an ID card or credit card
abstract sig Status{}
sig Valid,Expired extends Status{}

sig IDCard{
	status : one Status
}
sig CreditCard{
	status : one Status
}

//a human person can be near some cars, being driving one or be able to open one
sig Person{
		near : set Car,
		canOpen : set Car
}{
	canOpen in near
	all c: Car | c in canOpen <=> (this in User || this in Employee)
}

//a user has an ID card and a credit card, can have at most one active reservation
sig User extends Person{
	id : one IDCard,
	paymentInfo : one CreditCard,
	activeReservation : lone Reservation,
	pendingPayment : lone PaymentRequest
}{
	all c: Car | c in canOpen <=>  ( one r : Reservation | r.reservingUser = this && r.status in Active  && r.wasUsed in Unused )
}

//an employee can be notified of several retrieval request, and have accepted at most one of them 
sig Employee extends Person{
	acceptedRequest : lone RetrievalRequest,
	notifiedRequests : set RetrievalRequest
}{
	acceptedRequest in notifiedRequests
	canOpen in acceptedRequest.carToRetrieve
}

//a ride has a driver, a car, can result from a reservation and generate a payment request. A discount and extra fees can be applied
sig Ride{
	driver : one Person,
	car : one Car,
	reservedBy : lone Reservation,
	paymentGenerated : lone PaymentRequest
}{
	//only an employee does not pay for a ride if he/she needs to re trieve a car
	#paymentGenerated = 0 <=> car in driver.acceptedRequest.carToRetrieve
	//if a payment is generated, a user reserved the car and used it
	#paymentGenerated > 0 => (#reservedBy > 0 && reservedBy.wasUsed in Used)

	#paymentGenerated.discount > 0 || #paymentGenerated.extraFees > 0 => car.state not in InUse

	paymentGenerated.discount in TwoPlusPassengers =>  #car.passengers > 2
	paymentGenerated.discount in  Plugged => car.position in SpecialSafeArea
	paymentGenerated.discount in HighBattery => car.battery in MT50

	(one ex : ExtraFee | ex in paymentGenerated.extraFees && ex in NonSafe ) => car.position in NonSafeArea
}

sig PaymentRequest{
	discount : lone Discount,
	extraFees : set ExtraFee
}{
	#discount > 0 => #extraFees = 0
	
	
}

abstract sig Discount{}
sig TwoPlusPassengers, HighBattery, Plugged extends Discount{}

abstract sig ExtraFee{}
sig NonSafe, LowBattery, FarFromPowerGrid extends ExtraFee{}



//ASSERTIONS
assert openCar{
	all r1, r2 : Reservation |
		r1.reservingUser = r2.reservingUser && 
		r1.status in Active && r2.status in Active => r1 = r2
}

check openCar for 3






