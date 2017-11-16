/*****************************************************************************
 *
 * DATA
 *
 *****************************************************************************/

// Vehicles
int     v          = ...;
range   Vehicles   = 1..v;

// Customers
int     CustomersNumber      = ...;
range   Customers            = 1..CustomersNumber;
range   CustomersAndDepots   = 0..(CustomersNumber+1); // includes the starting depot and the returning depot

// Capacity
int Capacity = ...;

// Demand
int Demand[Customers] = ...;

// Time windows
int LBTW[CustomersAndDepots] = ...; // Lower Bound of the Time Window
int UBTW[CustomersAndDepots] = ...; // Upper Bound of the Time Window

int   ServiceTime[CustomersAndDepots] = ...;
int   XCoord[CustomersAndDepots] = ...;
int   YCoord[CustomersAndDepots] = ...;
float Distance[CustomersAndDepots][CustomersAndDepots]; // Cost or distance between i and j
float Time[CustomersAndDepots][CustomersAndDepots]; // Cost or distance between i and j

execute INITIALIZE {
	for(var i in CustomersAndDepots) {
		for (var j in CustomersAndDepots){
			if (i == j) {
				Distance[i][j] = 0;
				Time[i][j] = 0;
			} else {
			    Distance[i][j] = Math.floor(Math.sqrt(Math.pow(XCoord[i]-XCoord[j], 2) + Math.pow(YCoord[i]-YCoord[j], 2))*10)/10;
		        Time[i][j] = Distance [i][j] + ServiceTime[i];
	       	}
	     }
     }
}

// Decision variables
dvar boolean x[Vehicles][CustomersAndDepots][CustomersAndDepots]; // 1 if a vehicle drives directly from vertex i to vertex j
dvar int s[Vehicles][CustomersAndDepots]; // the time a vehicle starts to service a customer

/*****************************************************************************
 *
 * MODEL
 *
 *****************************************************************************/
minimize sum(k in Vehicles, i,j in CustomersAndDepots) (Distance[i][j]*x[k][i][j]);

subject to {
	forall(i in CustomersAndDepots, k in Vehicles)
	  x[k][i][i] == 0;

   // Each customer is visited exactly once
   forall (i in Customers)
    sum(k in Vehicles, j in CustomersAndDepots) x[k][i][j] == 1;

   // A vehicle can only be loaded up to it's capacity
   forall(k in Vehicles)
     	sum(i in Customers, j in CustomersAndDepots)(Demand[i] * x[k][i][j]) <= Capacity;

   // Each vehicle must leave the depot 0
   forall(k in Vehicles)
     	sum (j in CustomersAndDepots)x[k][0][j] == 1;

   // After a vehicle arrives at a customer it has to leave for another destination
   forall(h in Customers, k in Vehicles)
     	sum(i in CustomersAndDepots)x[k][i][h] - sum(j in CustomersAndDepots)x[k][h][j] == 0;

   // All vehicles must arrive at the depot n + 1
   forall(k in Vehicles)
     	sum (i in CustomersAndDepots) x[k][i][CustomersNumber+1] == 1;

   // The time windows are observed
   forall(i in CustomersAndDepots, k in Vehicles)
     	LBTW[i] <= s[k][i] <= UBTW[i];

   // From depot departs a number of vehicles equal to or smaller than v
   forall(k in Vehicles, j in CustomersAndDepots)
     	sum (k in Vehicles, j in CustomersAndDepots) x[k][0][j] <= v;

   // Vehicle departure time from a customer and its immediate successor
   forall(i,j in CustomersAndDepots, k in Vehicles)
     	s[k][i] + Time[i][j] - 1000*(1 - x[k][i][j]) <= s[k][j];
};

execute DISPLAY {
    writeln("Solutions: ");
    for(var k in Vehicles)
      for(var i in CustomersAndDepots)
    	  for (var j in CustomersAndDepots)
          if(x[k][i][j] == 1)
            writeln("vehicle ", k, " from ", i, " to ", j);
}
