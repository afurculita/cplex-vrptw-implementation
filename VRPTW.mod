/*****************************************************************************
 *
 * Vehicle Routing Problem with Time Windows (VRPTW)
 *
 * Three-index flow formulation with big-M time propagation constraints
 * (Solomon & Desrosiers 1988; Toth & Vigo, "Vehicle Routing", chapter 5).
 *
 * A fleet of v identical vehicles of capacity Capacity, based at node 0,
 * must serve every customer 1..CustomersNumber exactly once within the
 * customer's time window [LBTW, UBTW] and return to the depot, which is
 * duplicated as node CustomersNumber + 1 so every route is a path from
 * node 0 to node CustomersNumber + 1.  The objective is the total distance.
 *
 * Written for IBM ILOG CPLEX Optimization Studio 22.2.  See VRPTW2.mod for
 * the two-index formulation (recommended for identical vehicles) and
 * VRPTW_CP.mod for a CP Optimizer model.
 *
 *****************************************************************************/

/*****************************************************************************
 * DATA
 *****************************************************************************/

// Fleet
int   v        = ...;       // number of identical vehicles
range Vehicles = 1..v;

// Nodes: 0 = depot, 1..n = customers, n + 1 = copy of the depot (route end)
int   CustomersNumber = ...;
range Customers       = 1..CustomersNumber;
range Nodes           = 0..CustomersNumber+1;
int   Depot           = 0;
int   EndDepot        = CustomersNumber + 1;

int Capacity          = ...;
int Demand[Customers] = ...;

int LBTW[Nodes]        = ...;  // Earliest start of service (time window lower bound)
int UBTW[Nodes]        = ...;  // Latest start of service (time window upper bound)
int ServiceTime[Nodes] = ...;
int XCoord[Nodes]      = ...;
int YCoord[Nodes]      = ...;

// Euclidean distance truncated to one decimal, the Solomon benchmark convention.
float Distance[i in Nodes][j in Nodes] =
  floor(sqrt((XCoord[i] - XCoord[j]) * (XCoord[i] - XCoord[j])
           + (YCoord[i] - YCoord[j]) * (YCoord[i] - YCoord[j])) * 10) / 10.0;

// Time needed to go from i to j: service at i, then travel.
float Time[i in Nodes][j in Nodes] = Distance[i][j] + ServiceTime[i];

// Time windows tightened in preprocessing (Desrochers, Desrosiers & Solomon
// 1992).  Every route feasible for [LBTW, UBTW] is feasible for [Ready, Due],
// so the optimum is unchanged, but more arcs are pruned and every big-M is
// smaller.  Two necessary conditions are iterated to a fixed point:
//   Ready[j] >= min over predecessors i of Ready[i] + Time[i][j]
//   Due[j]   <= max over successors  k of Due[k]   - Time[j][k]
float Ready[Nodes];
float Due[Nodes];
execute TIGHTEN_TIME_WINDOWS {
  for (var i in Nodes) {
    Ready[i] = LBTW[i];
    Due[i] = UBTW[i];
  }
  var changed = true;
  var rounds = 0;
  while (changed && rounds < 100) {
    changed = false;
    rounds = rounds + 1;
    for (var j in Customers) {
      var earliest = Infinity;
      for (var i in Nodes) {
        if (i != j && i != EndDepot && Ready[i] + Time[i][j] <= Due[j]) {
          earliest = Math.min(earliest, Ready[i] + Time[i][j]);
        }
      }
      if (earliest != Infinity && earliest > Ready[j] + 1e-9) {
        Ready[j] = earliest;
        changed = true;
      }
      var latest = -Infinity;
      for (var k in Nodes) {
        if (k != j && k != Depot && Ready[j] + Time[j][k] <= Due[k]) {
          latest = Math.max(latest, Due[k] - Time[j][k]);
        }
      }
      if (latest != -Infinity && latest < Due[j] - 1e-9) {
        Due[j] = latest;
        changed = true;
      }
    }
  }
}

// Arcs that can never be part of a route: self loops, arcs into the start
// depot, arcs out of the end depot and arcs incompatible with the time windows.
int Allowed[i in Nodes][j in Nodes] =
  (i != j && j != Depot && i != EndDepot && Ready[i] + Time[i][j] <= Due[j]) ? 1 : 0;

// Tightest valid big-M for the time propagation constraint of each arc.
float BigM[i in Nodes][j in Nodes] = maxl(0, Due[i] + Time[i][j] - Ready[j]);

// Lower bound on the number of vehicles needed (capacity cut).
float TotalDemand = sum(i in Customers) Demand[i];

/*****************************************************************************
 * DECISION VARIABLES
 *****************************************************************************/

// x[k][i][j] = 1 if vehicle k travels directly from node i to node j
dvar boolean x[Vehicles][Nodes][Nodes];

// s[k][i] = time at which vehicle k starts servicing node i (bounded by the window)
dvar float s[k in Vehicles][i in Nodes] in Ready[i]..Due[i];

dexpr float TotalDistance = sum(k in Vehicles, i, j in Nodes) Distance[i][j] * x[k][i][j];
dexpr int   VehiclesUsed  = sum(k in Vehicles, j in Customers) x[k][Depot][j];

/*****************************************************************************
 * SOLVER SETTINGS
 *****************************************************************************/

execute PARAMS {
  cplex.tilim = 600;        // time limit in seconds
  cplex.epgap = 1e-4;       // relative MIP gap (CPLEX default)
  cplex.mipemphasis = 0;    // 0 balanced, 1 feasibility, 2 optimality, 3 best bound
  cplex.threads = 0;        // 0 = automatic
}

/*****************************************************************************
 * MODEL
 *****************************************************************************/

// Total distance.  For the Solomon benchmark convention (fewest vehicles
// first, then shortest distance) use instead:
//   minimize staticLex(VehiclesUsed, TotalDistance);
minimize TotalDistance;

subject to {

  // Arcs that can never be used
  forall(k in Vehicles, i, j in Nodes : Allowed[i][j] == 0)
    ctForbiddenArc:
      x[k][i][j] == 0;

  // Each customer is served exactly once, by exactly one vehicle
  forall(i in Customers)
    ctServeOnce:
      sum(k in Vehicles, j in Nodes) x[k][i][j] == 1;

  // A vehicle can only be loaded up to its capacity
  forall(k in Vehicles)
    ctCapacity:
      sum(i in Customers, j in Nodes) Demand[i] * x[k][i][j] <= Capacity;

  // Each vehicle leaves the depot exactly once (an idle vehicle goes
  // straight to the end depot at zero cost)
  forall(k in Vehicles)
    ctLeaveDepot:
      sum(j in Nodes) x[k][Depot][j] == 1;

  // Flow conservation: a vehicle that arrives at a customer also leaves it
  forall(k in Vehicles, h in Customers)
    ctFlowConservation:
      sum(i in Nodes) x[k][i][h] == sum(j in Nodes) x[k][h][j];

  // Each vehicle ends its route at the end depot exactly once
  forall(k in Vehicles)
    ctReturnToDepot:
      sum(i in Nodes) x[k][i][EndDepot] == 1;

  // Capacity cut: at least ceil(total demand / capacity) vehicles are needed
  ctMinVehicles:
    VehiclesUsed >= ceil(TotalDemand / Capacity);

  // Time propagation: if vehicle k goes from i to j, service at j cannot
  // start before service at i has finished and the vehicle has travelled.
  // Together with the time window bounds this also eliminates sub-tours.
  forall(k in Vehicles, i, j in Nodes : Allowed[i][j] == 1)
    ctTimePropagation:
      s[k][i] + Time[i][j] - BigM[i][j] * (1 - x[k][i][j]) <= s[k][j];

  // Symmetry breaking for the identical vehicles: idle vehicles get the
  // highest indices (if vehicle k is idle then vehicle k + 1 is idle too)
  forall(k in Vehicles : k < v)
    ctSymmetry:
      x[k][Depot][EndDepot] <= x[k+1][Depot][EndDepot];
}

/*****************************************************************************
 * OUTPUT
 *****************************************************************************/

execute DISPLAY {
  writeln("Total distance: ", TotalDistance);
  writeln("Vehicles used: ", VehiclesUsed, " of ", v);
  for (var k in Vehicles) {
    if (x[k][Depot][EndDepot] > 0.5) {
      writeln("vehicle ", k, ": idle");
      continue;
    }
    var i = Depot;
    var line = "vehicle " + k + ": " + i + "@" + s[k][i];
    var steps = 0;
    while (i != EndDepot && steps <= CustomersNumber) {
      for (var j in Nodes) {
        if (x[k][i][j] > 0.5) {
          line = line + " -> " + j + "@" + s[k][j];
          i = j;
          break;
        }
      }
      steps = steps + 1;
    }
    writeln(line);
  }
}
