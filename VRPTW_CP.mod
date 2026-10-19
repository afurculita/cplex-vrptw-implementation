/*****************************************************************************
 *
 * Vehicle Routing Problem with Time Windows (VRPTW)
 * Constraint programming model for CP Optimizer.
 *
 * Each customer visit is an interval variable of length ServiceTime whose
 * start must lie in the time window.  For every vehicle there is an optional
 * copy of each visit; exactly one copy is present (alternative).  The visits
 * of a vehicle form a sequence that starts with the depot, ends with the end
 * depot and has no overlap, with the travel distance as transition time
 * between consecutive visits.  The objective is the total travel distance.
 *
 * CP Optimizer works with integers, so all times and distances are scaled by
 * 10 (the distances have one decimal).  Uses the same .dat files as
 * VRPTW.mod.  CP finds good solutions quickly on instances that are far too
 * large for the MIP models, but proves optimality less often.
 *
 * NOTE: this model has not been run in this repository's test-suite (CP
 * Optimizer is not part of the CPLEX Community Edition on PyPI); report any
 * problem running it with CPLEX Optimization Studio 22.2.
 *
 *****************************************************************************/

using CP;

/*****************************************************************************
 * DATA
 *****************************************************************************/

int   v        = ...;
range Vehicles = 1..v;

int   CustomersNumber = ...;
range Customers       = 1..CustomersNumber;
range Nodes           = 0..CustomersNumber+1;
int   Depot           = 0;
int   EndDepot        = CustomersNumber + 1;

int Capacity          = ...;
int Demand[Customers] = ...;

int LBTW[Nodes]        = ...;
int UBTW[Nodes]        = ...;
int ServiceTime[Nodes] = ...;
int XCoord[Nodes]      = ...;
int YCoord[Nodes]      = ...;

int Scale = 10;  // one decimal of distance = one unit of time

// Euclidean distance truncated to one decimal, then scaled to an integer.
int Dist[i in Nodes][j in Nodes] =
  ftoi(floor(sqrt((XCoord[i] - XCoord[j]) * (XCoord[i] - XCoord[j])
                + (YCoord[i] - YCoord[j]) * (YCoord[i] - YCoord[j])) * Scale));

int Duration[i in Nodes] = ServiceTime[i] * Scale;
int Earliest[i in Nodes] = LBTW[i] * Scale;
int Latest[i in Nodes]   = UBTW[i] * Scale;

// Transition matrix for noOverlap: minimal gap between the end of a visit
// of type i and the start of a visit of type j.
tuple Triplet {
  int id1;
  int id2;
  int value;
}
{Triplet} Transition = { <i, j, Dist[i][j]> | i, j in Nodes };

/*****************************************************************************
 * DECISION VARIABLES
 *****************************************************************************/

// One visit per node; the depot visits have zero length.
dvar interval visit[i in Nodes]
  in Earliest[i]..Latest[i] + Duration[i] size Duration[i];

// Optional copy of each visit for each vehicle.  The depot visits are
// present for every vehicle (idle vehicles have an empty route).
dvar interval vehicleVisit[k in Vehicles][i in Nodes]
  optional(i != Depot && i != EndDepot)
  in Earliest[i]..Latest[i] + Duration[i] size Duration[i];

// The route of each vehicle: the sequence of its present visits, typed by node.
dvar sequence route[k in Vehicles]
  in    all(i in Nodes) vehicleVisit[k][i]
  types all(i in Nodes) i;

// Distance travelled from each present visit to the next one on its route.
dexpr int LegDistance[k in Vehicles][i in Nodes] =
  presenceOf(vehicleVisit[k][i]) * Dist[i][typeOfNext(route[k], vehicleVisit[k][i], EndDepot, EndDepot)];

dexpr int TotalDistanceScaled = sum(k in Vehicles, i in Nodes) LegDistance[k][i];
dexpr int VehiclesUsed = sum(k in Vehicles) (sum(c in Customers) presenceOf(vehicleVisit[k][c]) >= 1);

/*****************************************************************************
 * SOLVER SETTINGS
 *****************************************************************************/

execute PARAMS {
  cp.param.TimeLimit = 600;
  cp.param.Workers = 0;  // 0 = automatic
}

/*****************************************************************************
 * MODEL
 *****************************************************************************/

minimize TotalDistanceScaled;

subject to {

  // Each customer is visited by exactly one vehicle
  forall(c in Customers)
    ctOneVehicle:
      alternative(visit[c], all(k in Vehicles) vehicleVisit[k][c]);

  forall(k in Vehicles) {
    // Routes start at the depot and end at the end depot
    ctFirst:
      first(route[k], vehicleVisit[k][Depot]);
    ctLast:
      last(route[k], vehicleVisit[k][EndDepot]);

    // No two visits of a vehicle overlap, and travelling takes time
    ctNoOverlap:
      noOverlap(route[k], Transition);

    // Vehicle capacity
    ctCapacity:
      sum(c in Customers) Demand[c] * presenceOf(vehicleVisit[k][c]) <= Capacity;
  }

  // Symmetry breaking: a vehicle is used only if the previous one is used
  forall(k in Vehicles : k < v)
    ctSymmetry:
      sum(c in Customers) presenceOf(vehicleVisit[k+1][c]) <= CustomersNumber * sum(c in Customers) presenceOf(vehicleVisit[k][c]);
}

/*****************************************************************************
 * OUTPUT
 *****************************************************************************/

execute DISPLAY {
  writeln("Total distance: ", TotalDistanceScaled / Scale);
  writeln("Vehicles used: ", VehiclesUsed, " of ", v);
  for (var k in Vehicles) {
    var line = "vehicle " + k + ": " + Depot;
    var count = 0;
    // Print the present visits of the vehicle in order of their start time.
    var remaining = new Array();
    for (var c in Customers) {
      if (vehicleVisit[k][c].present) {
        remaining[count] = c;
        count = count + 1;
      }
    }
    if (count == 0) {
      writeln("vehicle ", k, ": idle");
      continue;
    }
    for (var n = 0; n < count; n++) {
      var best = -1;
      for (var p = 0; p < count; p++) {
        var c = remaining[p];
        if (c >= 0 && (best < 0 || vehicleVisit[k][c].start < vehicleVisit[k][best].start)) {
          best = c;
        }
      }
      line = line + " -> " + best + "@" + (vehicleVisit[k][best].start / Scale);
      for (var p = 0; p < count; p++) {
        if (remaining[p] == best) {
          remaining[p] = -1;
        }
      }
    }
    writeln(line + " -> " + EndDepot);
  }
}
