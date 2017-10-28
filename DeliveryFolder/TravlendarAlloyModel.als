open util/boolean
open util/integer

sig string {}

sig User {
	username: one string,
	email: one string,
	realizes: some Appointment,
	preferences: one Preferences
}

sig LocalTime{
	time: one Int
}{time >= 0}

abstract sig Appointment{
	description: lone string,
	located: one Location,
	has: some TravelMean,
	time: one Time,
	status: one AppointmentStatus
}

enum AppointmentStatus{ 
	created,
	started, 
	finished
}

sig FixedAppointment extends Appointment{}

sig FlexibleAppointment extends Appointment{
	minDuration: one Int
}{minDuration > 2}

sig Time{
	start: one Int,
	end: one Int 
}{start >= 0 end >= 0}


sig Location{
	latitude: one Int,
	longitude: one Int,
	distance: one Int
} {distance > 0}

abstract sig TravelMean{
	reaches: one Location,
	active: one Bool
}

sig Car extends TravelMean{}

sig Bike extends TravelMean{}

sig PublicTransport extends TravelMean{}	

sig Walking extends TravelMean{}

sig Preferences{ 
	maxWalkingDistance: one Int,
	publicTransportActive: one Bool
}{maxWalkingDistance > 0}

/*FACTS*/

fact usernameUnique{
	//User username is unique
	all disj u1, u2: User | u1.username != u2.username
}

fact emailUnique{
	//User email is unique
	all disj u1, u2: User | u1.email != u2.email
}

fact appointmentRealisedByOnly1User{
	//An appointment can only be realised by one user
	all disj u1, u2: User | u1.realizes & u2.realizes=none
}

fact appointmentDoesntExistWithoutUser{
	//Appointment shall not exist when not associated with a User
	all a1: Appointment | one u1: User | a1 in u1.realizes
}

fact timeDoesntExistWithoutAppointment{
	//Time shall not exist when not associated with an Appointment
	all t1: Time | one a1: Appointment | t1 in a1.time
}

fact preferencesDontExistWithoutUser{
	//Preferences shall not exist when not associated with a User
	all p1: Preferences | one u1: User | u1.preferences=p1
}

fact locationDoesntExistWithoutAppointment{
	//A location shall not exist when not associated with an appointment
	all l1: Location | one a1: Appointment | a1.located=l1
}

fact startTimeSmallerThanEndTime{
	//An appointments start time has to be smaller than the end time
	all t1: Time | t1.start < t1.end
}

fact minDurationHasToBeIncludedInInterval{
	//The minimum duration of a flexible appointment has to "fit" in the time interval of the appointment
	all fa: FlexibleAppointment | sub[fa.time.end, fa.time.start] > fa.minDuration
}

fact FixedAppointmentsDontOverlap{
	//Two different Fixed Appointments can't overlap
	all disj f1, f2: FixedAppointment | (f1.time.end < f2.time.start || f2.time.end < f1.time.start)
}

fact ifTravelMeanIsUsedActiveIsTrue{
	//If a travel mean is used it has to be active
	all a1: Appointment, tv1: TravelMean | tv1 in a1.has implies tv1.active.isTrue 
}

fact travelMeanReachesAppointmentsLocation{
	//The travel mean chosen for an appointment has to reach the appointments location
	all a1: Appointment, tv1: TravelMean | tv1 in a1.has implies tv1.reaches = a1.located 
}

fact differentLocationsCannotHaveSameLongitudeAndLatitude{
	//Two locations can't be identical 
	no disj l1, l2: Location | (l1.latitude = l2.latitude && l1.longitude = l2. longitude)
}

fact flexibleAppointmentDoesntOverlapFlexibleAppointment{
	//Two different Flexible Appointments can't overlap if there's not enough space for the minDuration of both
	all disj fa1, fa2: FlexibleAppointment | (((fa1.time.start <= fa2.time.start) && (fa1.time.end <= fa2.time.end)) implies
																((sub[fa2.time.end, fa1.time.start] >= add[fa1.minDuration, fa2.minDuration]))) ||
															(((fa1.time.end <= fa2.time.start) && (fa1.time.end <= fa2.time.end)) implies
																((sub[fa2.time.end, fa1.time.start] >= add[fa1.minDuration, fa2.minDuration])))
}

fact flexibleAppointmentDoesntOverlapFixedAppointment{
	//A Flexible Appointments and a Fixed Appointment can't overlap if there's not enough space for the minDuration of the Flexible one
	all disj f: FixedAppointment, fa: FlexibleAppointment | sub[fa.time.end, f.time.end] > fa.minDuration
}

fact travelMeansNeedToMeetPreferences{
	//Simplified to two preferences, shows that the model stands nonetheless
	all u1: User, pt1: PublicTransport |  (pt1 in u1.realizes.has) implies 
			u1.preferences.publicTransportActive.isTrue
	all u1: User, w1: Walking | ((w1 in u1.realizes.has)) implies 
			(u1.preferences.maxWalkingDistance >= w1.reaches.distance)
}

fact appointmentStatusCoherence{
	//The Appointment status has to be coherent with the local time
	all a: Appointment | a.status = created <=> (one lt: LocalTime | lt.time < a.time.start)
	all a: Appointment | a.status = started <=> (one lt: LocalTime | (a.time.start <= lt.time) && (lt.time <= a.time.end))
	all a: Appointment | a.status = finished <=> (one lt: LocalTime | a.time.end <= lt.time)
}

fact minDurationCoherence{
	//Not a requirement, but needed to avoid overflow in Alloy
	all fa: FlexibleAppointment | fa.minDuration < 8
}

fact SingletonClasses{ // Singletons
#LocalTime=1
}


pred show{
#User=1
#FlexibleAppointment=2
#FixedAppointment=2
#TravelMean=5
}
run show for 5 but 5 int
