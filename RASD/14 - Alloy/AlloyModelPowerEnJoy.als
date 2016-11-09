//-------------- PowerEnJoy -------  RASD ----- ALLOY MODEL

open util/boolean

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
	wasUsed : one Bool,
	reservedCar : one Car,
	reservingUser : one User
}{
	status in Active => reservedCar.state in (Reserved + Unavailable + InUse)
	status in Active  => reservingUser.id.status in Valid && reservingUser.paymentInfo.status in Valid
	status in  Active => #reservingUser.pendingPayment = 0 
}

abstract sig ReservationStatus{}
sig Active, Inactive extends ReservationStatus{}

//a car has a state, a current position, can have a driver, passengers, and can be plugged  in a power grid
sig Car{
	state : one CarState,
	engine : one EngineSate,
	position : one CityArea,
	driver : lone Person,
	passengers : set Person,
	plugged : lone PowerGrid
}{
	//state specification for a car

	state in Available => position in SafeArea && ( no r : Reservation | r.reservedCar = this && r.status in Active ) && engine in Off

	state in Dislocated => position in NonSafeArea && ( no r : Reservation | r.reservedCar = this && r.status in Active ) && engine in Off

	state in Reserved => position in SafeArea && ( one r : Reservation | r.reservedCar = this && r.status in Active  && r.wasUsed.isFalse ) && engine in Off

	state in Unavailable => ( one r : Reservation | r.reservedCar = this && r.status in Active && r.wasUsed.isTrue )   && engine in Off

	state in InUse <=> engine in On

	//if and only if the engine is on, the car has a driver ( the moment when the driver enters the car and the engine is still off is not modeled ) and can have passengers
	engine in On <=> #driver > 0
	#passengers > 0 => engine in On
	
	//a car can be plugged in if and only if the engine is off
	#plugged > 0 <=> engine in Off && position in SpecialSafeArea
}

abstract sig CarState {}
sig Available, Reserved, Dislocated, Unavailable, InUse extends CarState{}

abstract sig EngineSate{}
sig On,Off extends EngineState{}

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
		driving : lone Car,
		canOpen : set Car
}{
	canOpen in near
	canOpen <=> this in User || this in Employee
}

//a user has an ID card and a credit card, can have at most one active reservation
sig User extends Person{
	id : one IDCard,
	paymentInfo : one CreditCard,
	activeReservation : lone Reservation,
	pendingPayment : lone PaymentRequest
}{
	canOpen <=>  ( one r : Reservation | r.reservingUser = this && r.status in Active  && r.wasUsed.isFalse )
}

//an employee can be notified of several retrieval request, and have accepted at most one of them 
sig Employee extends Person{
	acceptedRequest : lone RetrievalRequest,
	notifiedRequests : set RetrievalRequest
}

//a ride has a driver, a car, can result from a reservation and generate a payment request. A discount and extra fees can be applied
sig Ride{
	driver : one Person,
	car : one Car,
	reservedBy : lone Reservation,
	paymentGenerated : lone PaymentRequest,
	discount : lone Discount,
	extraFees : set ExtraFee
}

sig PaymentRequest{}

abstract sig Discount{}
sig TwoPlusPassengers, HighBattery, Plugged extends Discount{}

sig ExtraFee{}
sig NonSafe, LowBattery, FarFromPowerGrid extends ExtraFee{}





