sig Car{
	batteryLevel: one BatteryLevelPercentage,
	status: one CarStatus,
	usedBy: lone LoggedUser,
	reservedBy: lone LoggedUser,
	numberOfPassengers: Int,
}{
	numberOfPassengers >= 0
	numberOfPassengers <=5 //Assuming 5 seats per car
}

abstract sig User{}
sig LoggedUser extends User{}

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
	all c:Car | c.batteryLevel = Lower20Full implies c.status = NotAvailable
}

fact PassengersOnlyOnInUseCars{
	no c:Car | c.status != InUse and c.numberOfPassengers >0
}

fact AtLeastOnePassengerOnInUseCars{
	no c:Car | c.status = InUse and c.numberOfPassengers =0
}

pred show{}
run show for 4
