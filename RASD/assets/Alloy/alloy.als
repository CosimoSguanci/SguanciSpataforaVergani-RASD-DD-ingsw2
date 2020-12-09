//////////////////////////////////////////////////////////////////
//////////////////////////SIGNATURES///////////////////////////////
//////////////////////////////////////////////////////////////////

abstract sig User{
	userStatus: UserStatus
}
sig AppUser extends User{}
sig TicketMachineUser extends User{}
sig CallCenterUser extends User{}

sig Date{} //add day, month, year attributes ONLY IF used in assertions

sig Time{
	hour: Int,
	min: Int
}

abstract sig Reservation{
	code: Code,
	date: Date,
	time: Time,
	res: User -> GroceryShop,
	queueNumber: lone Code, 	//number present in the display shown only for TicketMachine users
	ticketMachineReservation: lone TicketMachine	//TM used for a reservation
//	status: one ReservationStatus,
//	user: one User,
//	shop: one GroceryShop
}//{ 
	//#res = 1
//}
sig Visit extends Reservation {}
sig Ticket extends Reservation {}

sig GroceryShop {
	capacity: Int,
	openingHour: Time,
	closingHour: Time
}{
	//Shops are open for a considerable time
	openingHour.hour < closingHour.hour 
}

sig Code {
	id: Int
}

abstract sig UserStatus{}
one sig BLOCKED extends UserStatus{}
one sig NORMAL extends UserStatus{}

abstract sig Status{}
one sig PLANNED extends Status{}		//reserved, not yet used
one sig EXPIRED extends Status{}		//time over
one sig ACTIVE extends Status{}			//user is inside the shop

sig ReservationStatus{
	resStatus: Reservation -> Status
}{
	#resStatus = 1
}

sig TicketMachine {
	shop: GroceryShop
}




////////////////////////////////////////////////////////////////
/////////////////////////FUNCTIONS//////////////////////////////
///////////////////////////////////////////////////////////////

//retrieves all the reservations for a given grogecyShop 
fun getShopReservations [g : GroceryShop]: set Reservation {
	(res.g).User //res.g are the reservation associated to shop g
}

//retrieves all the ACTIVE reservations given a set of Reservations as parameter
fun getActiveReservations [reservations: set Reservation]: set Reservation {
	((resStatus.ACTIVE).reservations).(resStatus.ACTIVE)
}

//retrieves all the PLANNED reservations given a set of Reservations as parameter
fun getPlannedReservations [reservations: set Reservation]: set Reservation {
	((resStatus.PLANNED).reservations).(resStatus.PLANNED)
}

//retrieves all the Tickets associated to a User
fun getUserTickets [u: User]: set Ticket {
	(res.GroceryShop).u
}

//retrieves all the Reservations associated to a User
fun getUserReservations [u: User]: set Reservation {
	(res.GroceryShop).u
}

//retrieves all the PLANNED tickets associated given a set of Tickets as parameter
fun getPlannedTickets [tickets: set Ticket]: set Ticket {
	((resStatus.PLANNED).tickets).(resStatus.PLANNED)
}




//////////////////////////////////////////////////////////////////
//////////////////////////////FACTS////////////////////////////////
//////////////////////////////////////////////////////////////////

//The number of active reservations is always less than the maximum capacity of the shop
fact activeReservationsLowerThanCapacity {
	all g: GroceryShop | 
		(let resInG = getShopReservations[g] |
			(let resActiveInG = getActiveReservations[resInG] |
				 #resActiveInG <= g.capacity
			)
		)			
}

//The number of PLANNED ticket for every AppUser is 0 or 1.
fact justATicketPerAppUser {
	all au: AppUser | 
		(let userTicket = getUserTickets[au] |
			(let userPlannedTicket = getPlannedTickets[userTicket] |
				#userPlannedTicket <= 1
			)
		)
}

//The number of PLANNED ticket for every CallCenterUser is 0 or 1.
fact justATicketPerCallCenterUser {
	all ccu: CallCenterUser | 
		(let userTicket = getUserTickets[ccu] |
			(let userPlannedTicket = getPlannedTickets[userTicket] |
				#userPlannedTicket <= 1
			)
		)
}

//It is not possible that two different tickets have same code
fact uniqueCodeForReservation {
	no disj r1, r2: Reservation | r1.code = r2.code
}

//The queueNumber is unique for a shop in a day
fact uniqueQueueNumber {
	no disj r1, r2: Reservation | 
		r1.date = r2.date and
		r1.queueNumber = r2.queueNumber and
		User.(r1.res) = User.(r2.res)
}

//Blocked users cannot have any ACTIVE reservation
fact noMoreTicketForBlockedUser {
	no u: User | u.userStatus = BLOCKED and 
		(#getActiveReservations[getUserReservations[u]] > 0)
}

//Blocked users cannot have any PLANNED reservation
fact noMoreTicketForBlockedUser {
	no u: User | u.userStatus = BLOCKED and 
		(#getPlannedReservations[getUserReservations[u]] > 0)
}

//TicketMachine users cannot be blocked
fact noBlockedTicketMachineUsers {
	no tmu: TicketMachineUser | tmu.userStatus = BLOCKED
}

//AppUsers can book just a single visit per day
fact onlyOneVisitForAppUserInADay {
	all au: AppUser | no disj v1, v2 : Visit |
		v1.date = v2.date and v1.(res.GroceryShop) = au and v2.(res.GroceryShop) = au
}

//CallCenterUsers can book just a single visit per day
fact onlyOneVisitForCallCenterUserInADay {
	all ccu: CallCenterUser | no disj v1, v2 : Visit |
		v1.date = v2.date and v1.(res.GroceryShop) = ccu and v2.(res.GroceryShop) = ccu
}

//TicketMachine reservation are valid only for the same shop of the TicketMachine
fact sameShopForTicketMachineReservations {
	all tmu: TicketMachineUser, r : Reservation |
		tmu.(r.res) = r.ticketMachineReservation.shop
}

//Reservation can be only for shops' opening hours 
fact reserveForOpeningHours {
	all r: Reservation | 
		(let g = User.(r.res) | 
			((r.time.hour > g.openingHour.hour) and (r.time.hour < g.closingHour.hour))
			or ((r.time.hour = g.openingHour.hour) and (r.time.min >= g.openingHour.min))
			or ((r.time.hour = g.closingHour.hour) and (r.time.min < g.closingHour.min))
		)
}

//Every GroceryShop has at least a TicketMachine
fact atLeastATicketMachineForEachShop { 
	no g: GroceryShop |
		no tm: TicketMachine |
			tm.shop = g
}

//A signle user cannot have more than one active reservation
fact singleUserCannotHaveMoreThanOneActiveReservation {
	no disj r1, r2: Reservation |
		r1.(ReservationStatus.resStatus) = ACTIVE and
		r2.(ReservationStatus.resStatus) = ACTIVE and
		(r1.res).GroceryShop = (r2.res).GroceryShop		
}

//There is just a Reservation Status for each Reservation
fact singleReservationStatusForAReservation {
	no disj rs1, rs2: ReservationStatus |
		(rs1.resStatus).Status = (rs2.resStatus).Status
}

//A single user cannot have more than 1 active or planned reservation for a single day
fact noMultiplePlannedOrActiveReservationForAUserInSingleDay {
	all disj r1, r2: Reservation |
		((r1.date = r2.date) and ((r1.res).GroceryShop = (r2.res).GroceryShop)) 
		implies ( (r1.(ReservationStatus.resStatus) = EXPIRED) 
					or (r2.(ReservationStatus.resStatus) = EXPIRED))
}

//Every Reservation has only a single Status associated to it
fact everyReservationHasJustOneStatus {
	all r: Reservation |
		#r.(ReservationStatus.resStatus) = 1
}




//////////////////////////////////////////////////////////////
/////////////////////////PREDICATES///////////////////////////
/////////////////////////////////////////////////////////////

//This predicate shows a possible model for a single GroceryShop, single User and single Reservation scenario
pred singleShopSingleUserReservation {
	#GroceryShop = 1
	#User = 1
	#Reservation = 1
}

//This predicate shows that a TicketMachine belongs to a GroceryShop
pred eachTicketMachineBelongToSingleGroceryShop {
	#GroceryShop = 3
	#TicketMachine = 5	//REMEMBER TO RUN AT LEAST FOR 7 
	#Ticket = 0
	#Visit = 0
	#Code = 0
	#User = 0
	#Time = 2
	#Date = 0
	#Reservation = 0
}

//More reservation for a single User: just ONE can be ACTIVE, just one can be a Ticket
pred moreReservationsForSingleUser {
	#Reservation = 6
	#AppUser = 1
	#TicketMachineUser = 0
	#CallCenterUser = 0
	#Date = 1
	#TicketMachine = 1
	#GroceryShop = 1
}

//This predicate proves that it is not possible to have more than #capacity inside the shop (ACTIVE reservations)
pred moreActiveReservationThanShopCapacity (u1: User, u2: User, 
											r1: Reservation, r2: Reservation, 
											rStatus1: ReservationStatus, rStatus2: ReservationStatus, 
											g: GroceryShop) {
//INSTANCE FOUND:
//By simply changing g.capacity (2 or more) it will correctly found an instance
	g.capacity = 1
	u1.(r1.res) = g
	u2.(r2.res) = g
	r1.(rStatus1.resStatus) = ACTIVE
	r2.(rStatus2.resStatus) = ACTIVE
	r1 != r2
}

//Blocked users cannot have Planned or Active Reservations
pred blockedUsersCannotHavePlannedOrActiveReservations (u1, u2: User,
								r1, r2, r3, r4, r5: Reservation) {
	u1.userStatus = NORMAL
	u2.userStatus = BLOCKED
	r1.(ReservationStatus.resStatus) = ACTIVE
	r2.(ReservationStatus.resStatus) = ACTIVE
	r3.(ReservationStatus.resStatus) = PLANNED
	r4.(ReservationStatus.resStatus) = PLANNED
	r5.(ReservationStatus.resStatus) = EXPIRED
	#Reservation = 5
	#GroceryShop = 1
	#TicketMachine = 1
	#Time = 2
	#Code = 5
	#User = 3 		
	//NO INSTANCE FOUND:	
	//#User = 2 shows a counterexample: 1 user blocked, 
	//the other one cannot have more than an active reservation
	r1 != r2 and r3 != r4
}


run blockedUsersCannotHavePlannedOrActiveReservations for 5
