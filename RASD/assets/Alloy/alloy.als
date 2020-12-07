abstract sig User{
	userStatus: one UserStatus
}
sig AppUser extends User{}
sig TicketMachineUser extends User{}
sig CallCenterUser extends User{}

sig Date{} //add day, month, year attributes ONLY IF used in assertions
sig Position{} //add GPS latitude and longitude IF used in assertions

sig Time{}

abstract sig Reservation{
	code: one Code,
	date: one Date,
	res: User -> one GroceryShop,
	queueNumber: lone Code, 	//number present in the display shown only for TicketMachine users
	ticketMachineReservation: lone TicketMachine	//TM used for a reservation
//	status: one ReservationStatus,
//	user: one User,
//	shop: one GroceryShop
}{ 
	#res = 1
}
sig Visit extends Reservation {}
sig Ticket extends Reservation {}

sig GroceryShop {
	capacity: one Int
}

sig Code {
	id: one String
}

abstract sig UserStatus{}
one sig BLOCKED extends UserStatus{}
one sig NORMAL extends UserStatus{}

abstract sig Status{}
one sig PLANNED extends Status{}		//reserved, not yet used
one sig EXPIRED extends Status{}		//time over
one sig ACTIVE extends Status{}			//user is inside the shop

sig ReservationStatus{
	resStatus: Reservation -> one Status
}{
	#resStatus = 1
}

sig TicketMachine {
	shop: one GroceryShop
}



//FUNCTIONS

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



//FACTS

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


//PREDICATES
pred show {}

run show for 10







