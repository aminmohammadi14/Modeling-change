# آزمون علامت و نرمال‌سازی، شامل عدم امکان هم‌زمان در دامنهٔ کوچک
using Test,JuMP,HiGHS
include("REVCS19_FIX20.jl")
const F=REVCSFix20
const C=F.Core20
@testset "normalized rays and all-column witness over nine leaves" begin
    function fac(m)
        z=@variable(m,[1:4],Bin)
        @constraint(m,z[1]+z[2]<=1);@constraint(m,z[3]+z[4]<=1)
        return z,(z[1]-z[2],z[3]-z[4]),()->round.(Int,value.(z))
    end
    function block(m,u)
        a,b=u;x=@variable(m,binary=true);y=@variable(m,lower_bound=0)
        w=@variable(m);fix(w,1.0)
        @constraint(m,x+y<=1-a)
        @constraint(m,x+y>=b+1)
        @constraint(m,(1+b)*y<=w)
        @objective(m,Min,2+y)
    end
    cols=[C.IntegerPattern([1],[k]) for k in 0:1]
    for a in -1:1,b in -1:1
        bits=[a==1,a== -1,b==1,b== -1]
        function ray(col,aware)
            d=C.farkas_audit_symbolic_master(col,fac,block,HiGHS.Optimizer;threads=1,seconds=12.,sign_aware=aware)
            fix.(d.z,bits;force=true)
            optimize!(d.model)
            return objective_value(d.model)
        end
        primal=map(cols) do p
            m=Model(HiGHS.Optimizer);set_silent(m);set_optimizer_attribute(m,"threads",1)
            block(m,(a,b)); C.fix_pattern!(m,p); optimize!(m)
            termination_status(m)==F.MOI.INFEASIBLE
        end
        r=ray(cols,true)
        @test r≈ray(cols,false) atol=1e-8
        @test (r>1e-7)==all(primal)
        @test ray(cols[1:1],true)+1e-8>=r
    end
    m=Model(HiGHS.Optimizer); set_silent(m);set_optimizer_attribute(m,"threads",1)
    x=@variable(m); @constraint(m,x<=0);@constraint(m,x>=1)
    @objective(m,Min,0);optimize!(m)
    @test termination_status(m)==F.MOI.INFEASIBLE
    @test F.g742_fix14_ray_audit(m).certificate_numerically_validated
end
