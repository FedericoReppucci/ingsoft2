//-------------- PowerEnJoy -------  RASD ----- ALLOY MODEL

sig Person{
		near : set Car,
		driving : lone Car,
		canOpen : set Car
}
sig User extends Person{
	id : one IDCard,
	paymentInfo : one CreditCard,
	activeReservation : lone Reservation
}
sig Employee extends Person{
	acceptedRequest : lone RetrievalRequest
	notifiedRequests : set RetrievalRequest
}

sig Reservation{
	reservedCar : one Car
	reservingUser : one User
}

sig RetrievalRequest{}

sig Car{
	state : one CarState,
	position : CityArea
//power grid
}

sig Ride{
	driver : one Person,
	car : one Car,
	reservedBy : lone Reservation
	paymentGenerated : lone PaymentRequest
//discounts
}

abstract sig CarState {}
sig Available, Reserved, Dislocated, Unavailable, InUse extends CarState{}

sig CityArea{}
sig SafeArea extends CityArea{}
sig NonSafeArea extends CityArea{}
sig SpecialSafeArea extends SafeArea{}

sig PowerGrid{}

sig PaymentRequest{}

sig IDCard{
	status : one Status
}
sig CreditCard{
	status : one Status
}

abstract sig Status{}
sig Valid,Expired extends Status{}
