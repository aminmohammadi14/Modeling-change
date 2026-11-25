using Test,JuMP,HiGHS
include("REVCS19_FIX20.jl")
const F=REVCSFix20
const MOI=F.MOI
@testset "solver evidence contracts" begin
    function model(st,bound,solution)
        opt=MOI.Utilities.MockOptimizer(MOI.Utilities.Model{Float64}())
        m=direct_model(opt)
        x=@variable(m,lower_bound=0)
        @objective(m,Min,x)
        callback = function (output)
            if solution===nothing
                MOI.Utilities.mock_optimize!(output,st,MOI.NO_SOLUTION)
            else
                MOI.Utilities.mock_optimize!(output,st,(MOI.FEASIBLE_POINT,[solution]))
            end
            MOI.set(output,MOI.ObjectiveBound(),bound)
        end
        MOI.Utilities.set_mock_optimize!(opt,callback)
        optimize!(m)
        return m
    end
    u,_=F.g742_fix13_realization("nominal")
    for st in (MOI.DUAL_INFEASIBLE,MOI.INFEASIBLE_OR_UNBOUNDED,MOI.NUMERICAL_ERROR)
        a=F.safe_min(model(st,10.0,nothing));@test a.lower==-Inf && !a.feasible
    end
    for b in (NaN,Inf)
        @test F.safe_min(model(MOI.TIME_LIMIT,b,nothing)).lower==-Inf
    end
    a=F.safe_min(model(MOI.TIME_LIMIT,1.,nothing));@test a.lower==1. && !a.feasible
    a=F.safe_min(model(MOI.TIME_LIMIT,1.,2.));@test a.lower==1. && a.upper==2. && a.feasible
    @test !F.safe_min(model(MOI.TIME_LIMIT,-2.,-1.)).feasible
    @test_throws ErrorException F.safe_min(model(MOI.TIME_LIMIT,3.,2.))
    for status in ("NUMERICAL_ERROR","INFEASIBLE_OR_UNBOUNDED")
        e=F.evidence("inner_physical_cost",u,status,1.,Inf)
        @test_throws ErrorException F.validate_lb(e,u)
    end
    @test_throws ErrorException F.validate_lb(F.evidence("inner_find_feasible_column",u,"OPTIMAL",0.,0.),u)
    @test !F.checkedgap(1.,prevfloat(1.),0.1)
    @test_throws ErrorException F.run(["--relative-gap=0","--relative-gap=0"])
end
