# آزمون‌های مصنوعی فقط برای ریاضیات اوراکل هستند.
using Test,JuMP,HiGHS,TOML,SHA
include("REVCS19_FIX20.jl")
const F=REVCSFix20
const C=F.Core20
pval(x)=C.IntegerPattern([1],[x])
@testset "finite 3 × 3 robust recourse" begin
    mktempdir() do out
        o=(output=out,seconds=30.0,tol=1e-6,threads=1)
        ref,_=F.g742_fix13_realization("nominal")
        function scenario(v,w)
            return F.create_uncertainty_scenario("test",3,Float64(v==1),Float64(v== -1),
                Float64(w==1),Float64(w== -1),[ref[k] for k in ("beta_wt_plus","beta_wt_minus",
                "beta_pv_plus","beta_pv_minus","psi_plus","psi_minus")]...)
        end
        function fac(m)
            z=@variable(m,[1:4],Bin)
            @constraint(m,z[1]+z[2]<=1); @constraint(m,z[3]+z[4]<=1)
            a=z[1]-z[2]; b=z[3]-z[4]
            return z,(a,b),()->scenario(round(Int,value(a)),round(Int,value(b)))
        end
        function block(m,u)
            a,b=u
            x=@variable(m,binary=true)
            y=@variable(m)
            @constraint(m,y>=a-4*x)
            @constraint(m,y>=-a-4*(1-x))
            @constraint(m,-6<=y<=6)
            @objective(m,Min,y+b+2)
        end
        function numeric(u)
            m=Model(HiGHS.Optimizer);set_silent(m);set_optimizer_attribute(m,"threads",1)
            block(m,(u["omega_u_plus"]-u["omega_u_minus"],u["omega_p_plus"]-u["omega_p_minus"]))
            return m
        end
        cols=pval.([0,1])
        q=Float64[]
        for a in -1:1,b in -1:1
            u=scenario(a,b); m=numeric(u); optimize!(m)
            vals=map(cols) do p
                lp=numeric(u);C.fix_pattern!(lp,p);optimize!(lp);objective_value(lp)
            end
            @test objective_value(m)≈minimum(vals)
            @test minimum(vals)<=first(vals)
            push!(q,minimum(vals))
        end
        F.ledger["active"]=[1]; F.ledger["cache"]=Dict{String,Any}()
        gate,_=F.separate21(o,cols,fac,block;check=(u,p)->F.audited_column(o,numeric,u,p))
        @test gate==:covered
        cost=F.cost21(o,cols,fac,block,numeric)
        @test cost!==nothing
        @test cost[1]≈maximum(q)
        @test F.checkedgap(maximum(q),cost[1],1e-6)
        function splitblock(m,u)
            a,b=u
            x=@variable(m,binary=true); y=@variable(m,lower_bound=-8.0)
            @constraint(m,x>=a); @constraint(m,x<=a+1)
            @constraint(m,y>=a*b+b*x)
            @objective(m,Min,y+3+2*x)
        end
        function splitnum(u)
            m=Model(HiGHS.Optimizer);set_silent(m);set_optimizer_attribute(m,"threads",1)
            splitblock(m,(u["omega_u_plus"]-u["omega_u_minus"],u["omega_p_plus"]-u["omega_p_minus"]))
            return m
        end
        F.ledger["active"]=[1];empty!(F.ledger["cache"])
        # برای این تست، عضویت و امکان‌پذیری را با LP مستقل و دامنهٔ کوچک چک می‌کنیم.
        function testcheck(u,p)
            m=splitnum(u);C.fix_pattern!(m,p); optimize!(m)
            return termination_status(m)==F.MOI.INFEASIBLE ? :excluded : :feasible
        end
        sep,_=F.separate21(o,cols,fac,splitblock;check=testcheck)
        @test F.ledger["active"]==[1,2]
        @test sep==:covered
        exact=maximum(Iterators.product(-1:1,-1:1)) do (a,b)
            m=splitnum(scenario(a,b));optimize!(m);objective_value(m)
        end
        result=F.cost21(o,cols,fac,splitblock,splitnum)
        @test result!==nothing && result[1]≈exact
        @test !F.checkedgap(1.001,1.0,0.5)
        @test !F.checkedgap(1.0,Inf,1.0)
        @test !F.checkedgap(NaN,2.,0.5)
        for (states,want) in [([:unknown,:excluded],:unknown),([:excluded,:excluded],:witness),
                              ([:excluded,:feasible],:partial)]
            @test first(F.classify_pool((u,i)->states[i],1:2,nothing))==want
        end
    end
end
