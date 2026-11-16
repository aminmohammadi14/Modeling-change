using Test, JuMP, SCIP
import MathOptInterface as MOI
include(joinpath(@__DIR__,"revcs_planning19.jl"))
# مثال کوچک برای مقایسهٔ سناریوی خروجی با شمارش مستقل است، نه دادهٔ مقاله.
function block(m,u)
    n=length(u)
    y=@variable(m,[1:n],Bin)
    x=@variable(m,[1:n],lower_bound=0.,upper_bound=2.)
    for i in 1:n
        j=mod1(i+1,n)
        @constraint(m,x[i]>=u[i]*(1-u[j]))
        @constraint(m,x[i]>=0.4u[j])
        @constraint(m,x[i]<=(1+u[i])*y[i])
    end
    @objective(m,Min,sum(2y[i]+i/n*x[i]+0.1u[i] for i in 1:n))
end
builder=u->begin m=RC.new_model();block(m,u);m end
factory=(m,n)->begin
    z=@variable(m,[1:n],Bin)
    (z,z,()->round.(Int,value.(z)))
end
@testset "Worst-scenario, gap and bounds against enumeration" begin
    for n in 2:6
        points=[digits(k;base=2,pad=n) for k in 0:2^n-1]
        costs=Float64[]
        for b in points
            m=builder(b);optimize!(m)
            @test termination_status(m)==MOI.OPTIMAL
            push!(costs,objective_value(m))
        end
        exact=maximum(costs)
        r=RC.solve_native_ccg(builder,m->factory(m,n),block,zeros(Int,n);
            optimizer=SCIP.Optimizer,scope="worst scenario $n",seconds=30.,rtol=1e-7)
        @test r.converged
        @test r.lower<=exact+1e-6 && r.upper>=exact-1e-6
        @test RC.gap_closed(r.lower,r.upper,1e-7)
        m=builder(r.scenario);optimize!(m)
        @test termination_status(m)==MOI.OPTIMAL
        @test objective_value(m)≈exact atol=1e-6
    end
end
