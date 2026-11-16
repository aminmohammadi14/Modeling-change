# محک ریشهٔ واقعی 33P–12U؛ این اجرای محدود، حل مقاوم افق کامل نیست.
include(joinpath(@__DIR__,"revcs_planning19.jl"))
function run_root()
    g=state_grids(charging_kw=100.,storage_kwh=40.,pv_kw=60.)
    p=physical_problem(g;capacity_mode=:installed_capacity)
    started=time()
    d=planning_decision(p,PlanningArchive(3),1,p.initial,nominal_scenario(1);
        seconds=30.,require_optimal=true)
    println("ROOT_STATUS=",d.bounds.status)
    println("SOLVER_FEASIBLE_INCUMBENT=",d.bounds.feasible)
    println("FORWARD_ACCEPTED=",d.feasible)
    println("ROOT_LOWER_APPROXIMATION_BOUND=",d.bounds.lower)
    println("ROOT_INCUMBENT=",d.bounds.upper)
    println("BUILD_AND_SOLVE_SECONDS=",time()-started)
    println("WHOLE_HORIZON_ROBUST_UB=Inf (not computed)")
    write_rows(joinpath(@__DIR__,"root_solver_trace.csv"),RC.SOLVER_TRACE)
end
run_root()
