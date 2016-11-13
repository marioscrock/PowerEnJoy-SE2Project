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

//Car statuses
abstract sig CarStatus{}
one sig Available extends CarStatus{}
one sig Reserved extends CarStatus{}
one sig InUse extends CarStatus{}
one sig NotAvailable extends CarStatus{}

//Battery level percentage: should be a percentage 0-100%
abstract sig BatteryLevelPercentage{}
one sig Lower20Full extends BatteryLevelPercentage{} 
one sig More50Full extends BatteryLevelPercentage{}
one sig From20to50Full extends BatteryLevelPercentage{} 

//Number of passengers, we assume to deal with 5 passengers cars
abstract sig NOPType{}
one sig Zero extends NOPType{}
one sig One extends NOPType{}
one sig Two extends NOPType{}
one sig Three extends NOPType{}
one sig Four extends NOPType{}
one sig Five extends NOPType{}

abstract sig User{}
sig LoggedUser extends User{
	//personal information
	//other parameters
	banned: one Bool
}

sig ChargingStation{
	charging: set Car
}

//A RentMade models a rent made in the past, so, for example, in the world created 
//the user who made the rent can be banned or the car used for the rent can be NotAvailable

//If a RentMade corresponds to a reservation expired the corrispondent fee is assigned but
//others parameters regarding the end of the rent are set to default acceptable values

//leftMSOstation: true iff money saving option enabled and auto left on the station determined by MSO 

//Choice of discount to be applied is not modeled
sig RentMade{
	userRent: one LoggedUser,
	carRent: one Car,
	endPosition: one PositionWrtPowerGrid,
	endSafeArea: one Bool,
	reservationExpired: one Bool,
	endBatteryLevel: one BatteryLevelPercentage,
	onChargeAtTheEnd: one Bool,
	passengersDuringTheRide: one NOPType,
	discountApplicableRent: set Discount,
	additionalFeeRent: set Fee,
	leftMSOstation: one Bool
}

abstract sig PositionWrtPowerGrid{}
one sig More3kmPowerGrid extends PositionWrtPowerGrid{}
one sig Lower3kmPowerGrid extends PositionWrtPowerGrid{}

//M2PD = MoreThan2PassengersDiscount
//BHFD = BatteryHalfFullDiscount
//CCD = CarOnChargeDiscount
//MSOD = MoneySavingOptionDiscount
abstract sig Discount{}
one sig M2PD extends Discount{}
one sig BHFD extends Discount{}
one sig CCD extends Discount{}
one sig MSOD extends Discount{}

//REF =ReservationExpiredFee
//OSAF =OutSafeAreaFee
//A3BCF =Away3kmOrCSBatteryCriticalFee
abstract sig Fee{}
one sig REF extends Fee{}
one sig OSAF extends Fee{}
one sig A3BCF extends Fee{}

//A user can be only in one car at a given time
fact OneUserCanBeInOneCarAtSameTime{
	no disjoint c1,c2:Car | c1.usedBy = c2.usedBy and c1.usedBy != none
}

//A user can reserve only one car at a given time
fact ACarReservedByOnlyOneUser{
	no disjoint c1,c2:Car | c1.reservedBy = c2.reservedBy and c1.reservedBy != none
}

//A car in use cannot be reserved
fact ACarInUseCannotBeReserved{
    all c:Car | c.usedBy != none implies c.reservedBy = none
}

//A user cannot use one car and reserve another car at a given time
fact NoUsersCanUseAndReserveDifferentCars{
	no disjoint c1,c2:Car | c1.usedBy = c2.reservedBy and c1.usedBy != none and c2.reservedBy != none
}

//Cars set as Available cannot be used or reserved at a given time
fact AvaialableCarsCantBeReservedOrUsed{
	no c:Car | c.status = Available and (c.usedBy != none or c.reservedBy != none)
}

//Cars set as Not Available cannot be used or reserved at a given time
fact NotAvaialableCarsCantBeReservedOrUsed{
	no c:Car | c.status = NotAvailable and (c.usedBy != none or c.reservedBy != none)
}

//Reserved statuts must be paired with only one user
fact ReservedStatusMustBePairedWithOneUser{
	all c:Car | c.status = Reserved implies (c.reservedBy != none and c.usedBy = none)
}

//In Use statuts must be paired with only one user
fact InUseStatusMustBePairedWithOneUser{
	all c:Car | c.status = InUse implies (c.reservedBy = none and c.usedBy != none)
}

//Car with battery percentage lower than 20 percent full must be set as Not Available 
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


fact ReservationExpiredFeeApplicable{
	all r:RentMade | r.reservationExpired = True iff (REF in r.additionalFeeRent and #r.additionalFeeRent = 1)
	no r:RentMade | r.reservationExpired = False and REF in r.additionalFeeRent
}

fact NoReservationExpiredOutsideSafeArea{
	no r:RentMade | r.reservationExpired = True and r.endSafeArea = False
}

fact NoDiscountOrFeeIfReservationExpires{
	all r:RentMade | r.reservationExpired = True implies r.discountApplicableRent = none 
}

fact NoPassengersIfReservationExpires{
	all r:RentMade | r.reservationExpired = True iff r.passengersDuringTheRide = Zero
}

fact M2PDiscountAppliable{
	all r:RentMade |( r.passengersDuringTheRide != Zero and r.passengersDuringTheRide != One) 
		iff M2PD in r.discountApplicableRent
}

fact BHFDiscountAppliable{
	all r:RentMade | r.endBatteryLevel  = More50Full
		iff BHFD in r.discountApplicableRent
}

fact CCDiscountAppliable{
	all r:RentMade | r.onChargeAtTheEnd  = True
		iff CCD in r.discountApplicableRent
}

fact AllCharginStationInSafeArea{
	all r:RentMade | r.onChargeAtTheEnd  = True implies r.endSafeArea = True
}

fact IfLeftMSOStationIsOnCharge{
	all r:RentMade | r.leftMSOstation = True implies r.onChargeAtTheEnd  = True
}

fact MSODiscountAppliable{
	all r:RentMade | r.leftMSOstation = True iff MSOD in r.discountApplicableRent
}

fact OSAFeeMustBeAdded{
	all r:RentMade | r.endSafeArea = False
		iff OSAF in r.additionalFeeRent
}

fact A3BCFeeMustBeAdded{
	all r:RentMade | r.endPosition  = More3kmPowerGrid
		implies  A3BCF in r.additionalFeeRent
	all r:RentMade | r.endBatteryLevel = Lower20Full
		implies  A3BCF in r.additionalFeeRent
	all r:RentMade | A3BCF in r.additionalFeeRent
		implies (r.endPosition  = More3kmPowerGrid or r.endBatteryLevel = Lower20Full)
}

fact NoA3BCFeeIfonCharge{
    no r:RentMade | r.onChargeAtTheEnd  = True and A3BCF in r.additionalFeeRent
}

fact NoCCDMoreThan3km{
	no r:RentMade | CCD in r.discountApplicableRent and r.endPosition = More3kmPowerGrid
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

assert NoOSAFIfOnChargeAtTheEndRent{
	no r:RentMade |  r.onChargeAtTheEnd  = True and OSAF in r.additionalFeeRent
}
check NoOSAFIfOnChargeAtTheEndRent

assert NoCCDAndA3BCF{
	no r:RentMade | CCD in r.discountApplicableRent and A3BCF in r.additionalFeeRent
}
check NoCCDAndA3BCF

assert NoMSODMoreThan3km{
	no r:RentMade | MSOD in r.discountApplicableRent and r.endPosition = More3kmPowerGrid
}
check NoMSODMoreThan3km

assert NoMSODAndA3BCF{
	no r:RentMade | MSOD in r.discountApplicableRent and A3BCF in r.additionalFeeRent
}
check NoMSODAndA3BCF

pred show{#charging > 2 some u:LoggedUser | u.banned = True}
run show for 10 but exactly 2 ChargingStation, exactly 4 Car, exactly 4 LoggedUser, exactly 2 RentMade
