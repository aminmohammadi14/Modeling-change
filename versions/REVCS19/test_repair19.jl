using Test, JuMP
import MathOptInterface as MOI
include(joinpath(@__DIR__,"revcs_planning19.jl"))

@testset "Exact Hamming no-good rejects only the witnessed binary state" begin
    points=[digits(i;base=2,pad=3) for i in 0:7]
    for forbidden in points, b in points
        m=RC.new_model();bits=@variable(m,[1:3],Bin)
        m[:revcs_output_state_bits]=bits
        @test add_exact_feasibility_nogoods!(m,[forbidden])==1
        for (v,k) in zip(bits,b);fix(v,k;force=true);end
        @objective(m,Min,0);optimize!(m)
        @test termination_status(m)==(b==forbidden ? MOI.INFEASIBLE : MOI.OPTIMAL)
    end
    m=RC.new_model();@variable(m,x,Bin);m[:revcs_output_state_bits]=[x]
    @test_throws ErrorException add_exact_feasibility_nogoods!(m,[[2]])
    @test_throws ErrorException add_exact_feasibility_nogoods!(m,[[0,1]])
end

@testset "Feasible time-limit is distinct from optimal recourse" begin
    timed=(;feasible=true,status=MOI.TIME_LIMIT,upper=4.)
    opt=(;feasible=true,status=MOI.OPTIMAL,upper=4.)
    @test accept_decision(timed,Inf,false)
    @test !accept_decision(timed,Inf,true)
    @test accept_decision(opt,Inf,true)
    @test !accept_decision(opt,3.,true)
end

@testset "Each uncertainty family is required" begin
    init=StageState(Float64.(existing_REVCS),existing_REVCS.*Cc_0,
        existing_REVCS.*Ce_0,existing_REVCS.*Cv_0)
    u=nominal_scenario(1)
    for key in ("xi_wt","zeta_pv","zeta_station_pv")
        bad=deepcopy(u);delete!(bad,key)
        @test_throws ErrorException build_stage_subproblem(1,init.z,init.Cc,init.Ce,init.Cv,bad)
        bad=deepcopy(u);bad[key]=zeros(1,1)
        @test_throws ErrorException build_stage_subproblem(1,init.z,init.Cc,init.Ce,init.Cv,bad)
    end
    @test count(>(0.),pv_profile)==56
    @test full_uncertainty_domain(2).cardinality==big(3)^1882
    m=Model();z,_,_=symbolic_uncertainty(m,2)
    @test length(z)==3764
end

@testset "Repair immediately discards prior root UB and saved policy" begin
    # مسئلهٔ ساختگی صرفاً جریان کنترل را می‌سنجد؛ اعداد آن ورودی مقاله نیستند.
    seen=Ref(0); target(t)="mock repair Q$t"
    build=function(t,prev,u;seconds=20.,kwargs...)
        m=RC.new_model(;seconds);x=@variable(m,binary=true)
        m[:revcs_output_state_bits]=[x]
        t==1 && fix(x,0.;force=true)
        if t==3
            fix(x,0.;force=true)
            @constraint(m,x>=u-prev)
        end
        @objective(m,Min,t==2 ? x : 0*x)
        return m,capture->(;state=round(Int,value(x)),immediate=objective_value(m),operations=Dict())
    end
    oracle=function(t,prev;direction,kwargs...)
        u=0
        if t==3 && direction==:upper
            seen[]+=1
            u=seen[]>=3 ? 1 : 0
        end
        hi=direction==:upper ? 2. : Inf
        RC.CCGResult(0.,hi,false,false,u,RC.IntegerPattern[],NamedTuple[],target(t),:mock,direction)
    end
    cut=(t,prev,u;kwargs...)->RC.BinaryCut(-100.,[0.],-100.,0.,false,target(t))
    problem=PlanningProblem(3,0,x->[x],target,oracle,build,cut,(t,u)->true,b->only(b))
    dir=mktempdir()
    r=run_improved_rddp(problem;iterations=2,seconds=10.,rtol=0.,
        max_feasibility_repairs=1,output_dir=dir,capture=false)
    @test any(e.phase=="feasibility_repair" for e in r.phase_log)
    @test r.reason==:feasibility_repair_iteration_limit
    @test r.upper==Inf && r.best_policy===nothing
    @test isempty(r.archive.upper[1])
    @test !isfile(joinpath(dir,"certified_policy.toml"))
    @test TOML.parsefile(joinpath(dir,"status.toml"))["upper"]==Inf
    @test any(e.phase=="forward" && e.screening_source=="lower_fallback" for e in r.phase_log)
    @test all(hasproperty(e,:screening_oracle_gap_closed) for e in r.phase_log)
end
