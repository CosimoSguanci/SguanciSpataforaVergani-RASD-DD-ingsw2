abstract sig User{}
sig AppUser extends User{}
sig TicketMachineUser extends User{}
sig CallCenterUser extends User{}

sig Date{} //add day, month, year attributes ONLY IF used in assertions
sig Position{} //add GPS latitude and longitude IF used in assertions

sig Time{}

abstract sig Reservation{
	code: one Code,
	date: one Date,
//	status: one ReservationStatus,
//	user: one User,
//	shop: one GroceryShop
	res: User -> one GroceryShop,
	queueNumber: lone Code 	//number present in the display shown only for TicketMachine users
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
one sig ACTIVE extends Status{}		//user is inside the shop

sig ReservationStatus{
	resStatus: Reservation -> one Status
}{
	#resStatus = 1
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

//retrieves all the Tickets associated to a User
fun getUserTickets [u: User]: set Ticket {
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

//PREDICATES
pred show {}

run show for 10







