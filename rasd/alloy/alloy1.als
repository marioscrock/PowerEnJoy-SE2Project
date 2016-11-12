open util/boolean

sig Car{
	batteryLevel: one BatteryLevelPercentage,
	status: one CarStatus,
	usedBy: lone LoggedUser,
	reservedBy: lone LoggedUser,
	numberOfPassengers: NOPType,
    onCharge: one Bool,
	engineOn: one Bool
}

// Car statuses
abstract sig CarStatus{}
one sig Available extends CarStatus{}
one sig Reserved extends CarStatus{}
one sig InUse extends CarStatus{}
one sig NotAvailable extends CarStatus{}

//BatteryLevelPercentage
abstract sig BatteryLevelPercentage{}
one sig Lower20Full extends BatteryLevelPercentage{} 
one sig More20Full extends BatteryLevelPercentage{} 

//NumberOfPassengers
abstract sig NOPType{}
one sig Zero extends NOPType{}
one sig One extends NOPType{}
one sig Two extends NOPType{}
one sig Three extends NOPType{}
one sig Four extends NOPType{}
one sig Five extends NOPType{}

abstract sig User{}
sig LoggedUser extends User{
	banned: one Bool
}

sig ChargingStation{
	charging: set Car
}

fact ACarUsedByOnlyOneUser{
	no disjoint c1,c2:Car | c1.usedBy = c2.usedBy and c1.usedBy != none
}

fact ACarReservedByOnlyOneUser{
	no disjoint c1,c2:Car | c1.reservedBy = c2.reservedBy and c1.reservedBy != none
																					//and c2.reservedBy != none
}

fact ACarInUseCannotBeReserved{
	//all u1,u2:User no c:Car|(c.usedBy=u1 and c.reservedBy=u1)
	//no c:Car | c.usedBy != none and c.reservedBy != none Così non ci sono macchine libere
    all c:Car | c.usedBy != none implies c.reservedBy = none
}

fact NoUsersCanUseAndReserveDifferentCars{
	no disjoint c1,c2:Car | c1.usedBy = c2.reservedBy and c1.usedBy != none and c2.reservedBy != none
}

fact AvaialableCarsCantBeReservedOrUsed{
	no c:Car | c.status = Available and (c.usedBy != none or c.reservedBy != none)
}

fact NotAvaialableCarsCantBeReservedOrUsed{
	no c:Car | c.status = NotAvailable and (c.usedBy != none or c.reservedBy != none)
}

fact ReservedStatusMustBePairedWithOneUser{
	all c:Car | c.status = Reserved implies (c.reservedBy != none and c.usedBy = none)
}

fact InUseStatusMustBePairedWithOneUser{
	all c:Car | c.status = InUse implies (c.reservedBy = none and c.usedBy != none)
}

fact CarWithBatteryPercentageLower20FullNotAvailable{
	all c:Car | (c.batteryLevel = Lower20Full and c.onCharge = False) implies c.status = NotAvailable
}

fact PassengersOnlyOnInUseCars{
	no c:Car | c.status != InUse and c.numberOfPassengers != Zero
}

fact AtLeastOnePassengerOnInUseCars{
	no c:Car | c.status = InUse and c.numberOfPassengers = Zero
}

fact OnlyInUseCarEngineOn{
	all c:Car | c.engineOn = True <=> c.status = InUse
}

fact InUseCarNotOnCharge{
	all c:Car | c.status = InUse implies c.onCharge = False
}

// A car is charging when connected to a charging station
fact CarIsChargingWhenConnected{
	all s:ChargingStation, c:Car | c in s.charging implies c.onCharge = True
	all c:Car | some s:ChargingStation | c.onCharge = True implies c in s.charging
}

// At most one charging station connected to a car
fact NoMoreOneCSForOneCar{
	all disjoint s1,s2:ChargingStation | s1.charging & s2.charging = none
}

fact NoBannedUsersDealingWithCars{
	no u:User | some c:Car | u.banned = True and ( c.usedBy = u or c.reservedBy = u )
}

// Assertions
assert NoReservedCarWithEngineOn{
	no c:Car | c.engineOn = True and c.status = Reserved
}
check NoReservedCarWithEngineOn

assert NoCarInChargeWithEngineOn{
	no c:Car | c.engineOn = True and c.onCharge = True
}
check NoCarInChargeWithEngineOn

/* REQUIREMENTS */
pred show{#charging > 2 #banned > 0}
run show for 10 but exactly 2 ChargingStation, exactly 6 Car, exactly 4 LoggedUser
