//-------------- PowerEnJoy -------  RASD ----- ALLOY MODEL

sig Person{}
sig User extends Person{}
sig Employee extends Person{}

sig Reservation{}
sig Car{}
sig Ride{}

abstract sig CarState {}
sig Available, Reserved, Dislocated, Unavailable, InUse extends CarState{}

sig CityArea{}
sig SafeArea extends CityArea{}
sig NonSafeArea extends CityArea{}

sig PowerGrid{}

sig PaymentRequest{}

sig IDCard{}
sig CreditCard{}

abstract sig Status{}
sig Valid,Expired extends Status{}
