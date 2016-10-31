sig Car{
	batteryLevel: Int, //Percentage, should be float
	status: one CarStatus,
	usedBy: lone LoggedUser,
	reservedBy: lone LoggedUser,
	numberOfPassengers: Int,
}{
	batteryLevel > 0
	batteryLevel<100
	numberOfPassengers > 0
	numberOfPassengers <=5 //Assuming 5 seats per car
}

abstract sig User{}
sig LoggedUser extends User{}

// Car statuses
abstract sig CarStatus{}
sig Available extends CarStatus{}
sig Reserved extends CarStatus{}
sig InUse extends CarStatus{}
sig NotAvailable extends CarStatus{}


fact ACarUsedByOnlyOneUser{
	no disjoint c1,c2:Car | c1.usedBy = c2.usedBy and c1.usedBy != none
}

fact ACarReservedByOnlyOneUser{
	no disjoint c1,c2:Car | c1.reservedBy = c2.reservedBy and c1.reservedBy != none and c2.reservedBy != none
}

fact ACarInUseCannotBeReserved{
	//all u1,u2:User no c:Car|(c.usedBy=u1 and c.reservedBy=u1)
	no c:Car | c.usedBy != none and c.reservedBy != none
}

fact NoUsersCanUseAndReserveDifferentCars{
	no disjoint c1,c2:Car | c1.usedBy = c2.reservedBy and c1.usedBy != none and c2.reservedBy != none
}

pred show{}
run show for 4
