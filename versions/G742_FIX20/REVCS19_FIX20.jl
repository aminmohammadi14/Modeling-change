# REVCS19 | Gate 7.4.2 | FIX20 | 33P–12U
# اجرای مستقیم در ترمینال: julia --project=. REVCS19_FIX20.jl
# در محیط تعاملی: include("REVCS19_FIX20.jl") سپس REVCSFix20.run()
# تمام منابع و داده‌های لازم در همین فایل هستند. محیط جولیا به JuMP، HiGHS، MOI و SCIP نیاز دارد.
module REVCSFix20
using SHA, Dates

const RUNTIME20=mktempdir()
const FIX20_RESUME=Ref{Union{Nothing,String}}(nothing)
# نسخهٔ اصلی مدل با بایت‌های اولیه روی دیسک موقت قرار می‌گیرد تا هویت گواه‌های پیشین حفظ شود.
function resource20(name,expected,source)
    bytes2hex(sha256(source))==expected || error("Embedded input checksum mismatch: $name")
    dest=joinpath(RUNTIME20,split(name,'/')...)
    mkpath(dirname(dest))
    write(dest,source)
end
function load_resources20()
    resource20("REVCS19_G7_4_2_FARKAS_AUDIT_HOOKS.jl","7217c5688e9829d51d161ae49f8080a52102d8b11200bb0b4bc3b4cda14ff6a6","""# REVCS19 Gate 7.4.2 FIX9 -- exact sign-aware L1 normalization diagnostic.
# This file adds diagnostic copies of the existing symbolic Farkas construction.
# It does not replace the production symbolic_master or modify the frozen physics.

@eval REVCSCertifiedCore begin
    farkas_audit_bump!(m::Dict{String,Int}, key::String, n::Int=1) =
        (m[key] = get(m,key,0) + n)

    function farkas_audit_binary_monomial!(m,key,z,and_cache,metrics)
        length(key)==1 && return z[only(key)]
        length(key)==2 || error(\"Only quadratic uncertainty terms supported\")
        return get!(and_cache,key) do
            b=@variable(m,binary=true)
            farkas_audit_bump!(metrics,\"and_aux_variables\")
            farkas_audit_bump!(metrics,\"and_binary_domain_constraints\")
            @constraint(m,b<=z[key[1]])
            @constraint(m,b<=z[key[2]])
            @constraint(m,b>=z[key[1]]+z[key[2]]-1)
            farkas_audit_bump!(metrics,\"and_linearization_constraints\",3)
            b
        end
    end

    function farkas_audit_indicator_product!(m,z,lambda,cache,metrics)
        key=(index(z).value,index(lambda).value)
        return get!(cache,key) do
            w=@variable(m)
            farkas_audit_bump!(metrics,\"binary_dual_product_variables\")
            lo=has_lower_bound(lambda) ? lower_bound(lambda) : -Inf
            hi=has_upper_bound(lambda) ? upper_bound(lambda) : Inf
            if isfinite(lo) && isfinite(hi)
                lo<=hi || error(\"Inconsistent certified dual bounds\")
                @constraint(m,w>=lo*z)
                @constraint(m,w<=hi*z)
                @constraint(m,w>=lambda-hi*(1-z))
                @constraint(m,w<=lambda-lo*(1-z))
                farkas_audit_bump!(metrics,\"binary_dual_product_constraints\",4)
                return w
            end
            complement=get!(cache,(:complement,index(z).value)) do
                b=@variable(m,binary=true)
                farkas_audit_bump!(metrics,\"complement_binary_variables\")
                farkas_audit_bump!(metrics,\"complement_binary_domain_constraints\")
                @constraint(m,b+z==1)
                farkas_audit_bump!(metrics,\"complement_constraints\")
                b
            end
            @constraint(m,z --> {w-lambda<=0})
            @constraint(m,z --> {lambda-w<=0})
            @constraint(m,complement --> {w<=0})
            @constraint(m,complement --> {-w<=0})
            farkas_audit_bump!(metrics,\"indicator_constraints\",4)
            w
        end
    end

    function farkas_audit_polynomial_times_dual!(m,p,lambda,z,and_cache,product_cache,metrics)
        e=AffExpr(0.0)
        for (key,c) in p
            c==0.0 && continue
            if isempty(key)
                add_to_expression!(e,c,lambda)
            else
                farkas_audit_bump!(metrics,\"binary_dual_product_terms\")
                length(key)==1 && farkas_audit_bump!(metrics,\"degree1_dual_product_terms\")
                length(key)==2 && farkas_audit_bump!(metrics,\"degree2_dual_product_terms\")
                b=farkas_audit_binary_monomial!(m,key,z,and_cache,metrics)
                add_to_expression!(e,c,farkas_audit_indicator_product!(m,b,lambda,product_cache,metrics))
            end
        end
        return e
    end

    function farkas_audit_add_symbolic_dual_column!(master,z,pattern,uncertainty_factory,symbolic_builder,
            metrics,primal_set_types; and_cache=Dict(),product_cache=Dict(),sign_aware=false)
        pm=Model()
        uz,unc,_=uncertainty_factory(pm)
        length(uz)==length(z) || error(\"Uncertainty layout changed between models\")
        snapshot=Set(all_constraints(pm;include_variable_in_set_constraints=true))
        symbolic_builder(pm,unc)
        uset=Set(uz)
        primal=filter(v->!(v in uset),all_variables(pm))
        ordinal=Dict(v=>i for (i,v) in enumerate(primal))
        iv=filter(v->is_binary(v)||is_integer(v),primal)
        [ordinal[v] for v in iv]==pattern.indices || error(\"Symbolic/oracle integer layouts differ\")
        integers=Dict(v=>k for (v,k) in zip(iv,pattern.values))
        continuous=Set(filter(v->!haskey(integers,v),primal))
        unc_index=Dict(v=>i for (i,v) in enumerate(uz))
        c0,c=split_parametric_expression(objective_function(pm),unc_index,integers,continuous)
        stationarity=Dict(v=>AffExpr(0.0) for v in continuous)

        farkas_audit_bump!(metrics,\"primal_variables_total\",length(primal))
        farkas_audit_bump!(metrics,\"primal_integer_variables\",length(iv))
        farkas_audit_bump!(metrics,\"primal_continuous_variables\",length(continuous))
        farkas_audit_bump!(metrics,\"uncertainty_domain_constraints_excluded\",length(snapshot))
        farkas_audit_bump!(metrics,\"integer_domain_constraints_skipped\",length(iv))

        for v in continuous
            coef=get(c,v,Poly15())
            any(!isempty(k)&&a!=0 for (k,a) in coef) && error(\"Uncertain continuous objective unsupported\")
        end

        dual_obj=AffExpr(0.0)
        # With sign-aware normalization, use the exact absolute-value expression
        # for sign-definite duals; retain the original epigraph for free duals.
        normvars=VariableRef[]
        normexpr=AffExpr(0.0)
        normalization_terms=0
        for con in all_constraints(pm;include_variable_in_set_constraints=true)
            con in snapshot && continue
            obj=constraint_object(con)
            if obj.set isa MOI.ZeroOne || obj.set isa MOI.Integer
                continue
            end
            farkas_audit_bump!(metrics,\"primal_constraints_dualized\")
            setname=string(typeof(obj.set))
            primal_set_types[setname]=get(primal_set_types,setname,0)+1
            off,A=split_parametric_expression(obj.func,unc_index,integers,continuous)
            pieces=if obj.set isa MOI.EqualTo
                ((:eq,obj.set.value),)
            elseif obj.set isa MOI.LessThan
                ((:le,obj.set.upper),)
            elseif obj.set isa MOI.GreaterThan
                ((:ge,obj.set.lower),)
            elseif obj.set isa MOI.Interval
                ((:ge,obj.set.lower),(:le,obj.set.upper))
            else
                error(\"Unsupported symbolic LP constraint \$(typeof(obj.set))\")
            end
            for (sense,rhs) in pieces
                sense==:eq && farkas_audit_bump!(metrics,\"equality_sides\")
                sense==:le && farkas_audit_bump!(metrics,\"less_equal_sides\")
                sense==:ge && farkas_audit_bump!(metrics,\"greater_equal_sides\")
                lambda=@variable(master)
                farkas_audit_bump!(metrics,\"dual_multiplier_variables\")
                sense==:le && set_upper_bound(lambda,0.0)
                sense==:ge && set_lower_bound(lambda,0.0)
                if sense==:eq
                    set_lower_bound(lambda,-1.0)
                    set_upper_bound(lambda,1.0)
                elseif sense==:le
                    set_lower_bound(lambda,-1.0)
                elseif sense==:ge
                    set_upper_bound(lambda,1.0)
                else
                    error(\"Unknown Farkas multiplier sign\")
                end
                farkas_audit_bump!(metrics,\"dual_variable_bound_constraints\",2)
                if sign_aware && sense != :eq
                    # Projection of original av >= +/-lambda and sum(av)<=1:
                    # for lambda <= 0, av may be replaced by -lambda;
                    # for lambda >= 0, av may be replaced by lambda.
                    coef = sense == :le ? -1.0 : 1.0
                    add_to_expression!(normexpr,coef,lambda)
                    farkas_audit_bump!(metrics,\"sign_aware_eliminated_abs_variables\")
                    farkas_audit_bump!(metrics,\"sign_aware_eliminated_abs_bound_constraints\",2)
                    farkas_audit_bump!(metrics,\"sign_aware_eliminated_abs_rows\",2)
                    sense == :le && farkas_audit_bump!(metrics,\"sign_aware_nonpositive_duals\")
                    sense == :ge && farkas_audit_bump!(metrics,\"sign_aware_nonnegative_duals\")
                else
                    av=@variable(master,lower_bound=0.0,upper_bound=1.0)
                    push!(normvars,av)
                    farkas_audit_bump!(metrics,\"absolute_value_variables\")
                    farkas_audit_bump!(metrics,\"absolute_value_bound_constraints\",2)
                    @constraint(master,av>=lambda)
                    @constraint(master,av>=-lambda)
                    farkas_audit_bump!(metrics,\"absolute_value_rows\",2)
                    if sign_aware
                        add_to_expression!(normexpr,1.0,av)
                        farkas_audit_bump!(metrics,\"sign_aware_free_duals_retained\")
                    end
                end
                normalization_terms+=1
                for (v,coeffs) in A
                    stationarity[v]+=farkas_audit_polynomial_times_dual!(master,coeffs,lambda,z,and_cache,product_cache,metrics)
                end
                rpoly=Poly15(k=>-a for (k,a) in off)
                addpoly!(rpoly,(),rhs)
                dual_obj+=farkas_audit_polynomial_times_dual!(master,rpoly,lambda,z,and_cache,product_cache,metrics)
            end
        end
        for v in continuous
            @constraint(master,stationarity[v]==0.0)
            farkas_audit_bump!(metrics,\"stationarity_rows\")
        end
        if normalization_terms > 0
            if sign_aware
                @constraint(master,normexpr<=1.0)
            else
                @constraint(master,sum(normvars)<=1.0)
            end
            farkas_audit_bump!(metrics,\"l1_normalization_rows\")
        end
        farkas_audit_bump!(metrics,\"columns_processed\")
        farkas_audit_bump!(metrics,\"integer_pattern_entries\",length(pattern.values))
        return dual_obj
    end

    # Small, solver-executed equivalence check, independent of the large REVCS model.
    # Lambda values cover both feasible and infeasible signed/free assignments.
    function farkas_audit_sign_normalization_selftest(;threads::Int=8)
        cases=[
            (0.0,-0.0,0.0),
            (0.2,-0.3,0.5),
            (-0.4,-0.5,0.1),
            (1.0,0.0,0.0),
            (-1.0,0.0,0.0),
            (0.2,-0.6,0.3),
            (0.0,-0.7,0.4),
            (0.0,-1.0,0.0),
            (0.1,-0.2,0.7),
            (-0.3,-0.4,0.3),
            (0.4,0.0,0.6),
            (-0.2,-0.2,0.6),
        ]
        results=NamedTuple[]
        for (i,values) in enumerate(cases)
            statuses=Bool[]
            for sign_aware in (false,true)
                m=Model(HiGHS.Optimizer)
                set_silent(m)
                set_optimizer_attribute(m,\"threads\",threads)
                norm=AffExpr(0.0)
                normvars=VariableRef[]
                for (sense,v) in zip((:eq,:le,:ge),values)
                    lam=@variable(m)
                    if sense==:eq
                        set_lower_bound(lam,-1.0);set_upper_bound(lam,1.0)
                    elseif sense==:le
                        set_lower_bound(lam,-1.0);set_upper_bound(lam,0.0)
                    else
                        set_lower_bound(lam,0.0);set_upper_bound(lam,1.0)
                    end
                    @constraint(m,lam==v)
                    if sign_aware && sense!=:eq
                        add_to_expression!(norm,sense==:le ? -1.0 : 1.0,lam)
                    else
                        av=@variable(m,lower_bound=0.0,upper_bound=1.0)
                        @constraint(m,av>=lam)
                        @constraint(m,av>=-lam)
                        if sign_aware
                            add_to_expression!(norm,1.0,av)
                        else
                            push!(normvars,av)
                        end
                    end
                end
                if sign_aware
                    @constraint(m,norm<=1.0)
                else
                    @constraint(m,sum(normvars)<=1.0)
                end
                @objective(m,Min,0.0)
                optimize!(m)
                status=termination_status(m)
                status in (MOI.OPTIMAL,MOI.INFEASIBLE) ||
                    error(\"FIX9_SELFTEST_SOLVER_INDETERMINATE_CASE_\$i status=\$status\")
                push!(statuses,status==MOI.OPTIMAL)
            end
            expected=sum(abs,values)<=1.0+1e-9
            statuses[1]==statuses[2]==expected ||
                error(\"FIX9_SELFTEST_EQUIVALENCE_FAILED_CASE_\$i\")
            push!(results,(;case_id=i,lambda_equal=values[1],lambda_nonpositive=values[2],
                lambda_nonnegative=values[3],legacy_feasible=statuses[1],
                sign_aware_feasible=statuses[2],analytical_feasible=expected,passed=true))
        end
        return results
    end

    function farkas_audit_symbolic_master(columns,uncertainty_factory,symbolic_builder,optimizer;
            seconds=90.0,threads::Int=g7cfg().threads,sign_aware::Bool=false)
        threads>0 || error(\"Farkas audit threads must be positive\")
        m=Model(optimizer)
        set_silent(m)
        # Match the existing HiGHS model-construction settings; this is solver configuration only.
        set_optimizer_attribute(m,\"presolve\",\"on\")
        set_optimizer_attribute(m,\"threads\",threads)
        set_time_limit_sec(m,Float64(seconds))
        metrics=Dict{String,Int}()
        primal_set_types=Dict{String,Int}()
        and_cache=Dict();product_cache=Dict()
        v0=num_variables(m)
        c0=num_constraints(m;count_variable_in_set_constraints=true)
        z,unc,extract=uncertainty_factory(m)
        metrics[\"uncertainty_variables\"]=num_variables(m)-v0
        metrics[\"uncertainty_constraints\"]=num_constraints(m;count_variable_in_set_constraints=true)-c0
        metrics[\"uncertainty_binary_indicators\"]=length(z)
        eta=@variable(m)
        metrics[\"eta_variables\"]=1
        set_lower_bound(eta,0.0)
        metrics[\"eta_bound_constraints\"]=1
        for p in columns
            dual=farkas_audit_add_symbolic_dual_column!(m,z,p,uncertainty_factory,symbolic_builder,
                metrics,primal_set_types;and_cache,product_cache,sign_aware)
            @constraint(m,eta<=dual)
            farkas_audit_bump!(metrics,\"column_link_rows\")
        end
        @objective(m,Max,eta)
        metrics[\"normalization_sign_aware_enabled\"]=sign_aware ? 1 : 0
        if sign_aware
            signed=get(metrics,\"sign_aware_eliminated_abs_variables\",0)
            expected_signed=get(metrics,\"less_equal_sides\",0)+get(metrics,\"greater_equal_sides\",0)
            signed==expected_signed || error(\"FIX9_SIGNED_DUAL_COUNT_MISMATCH\")
            get(metrics,\"absolute_value_variables\",0)==get(metrics,\"equality_sides\",0) ||
                error(\"FIX9_FREE_DUAL_ABS_COUNT_MISMATCH\")
            get(metrics,\"sign_aware_free_duals_retained\",0)==get(metrics,\"equality_sides\",0) ||
                error(\"FIX9_FREE_DUAL_RETAINED_MISMATCH\")
            get(metrics,\"sign_aware_eliminated_abs_rows\",0)==2signed ||
                error(\"FIX9_ELIMINATED_ABS_ROWS_MISMATCH\")
            metrics[\"legacy_projected_variables\"]=num_variables(m)+signed
            metrics[\"legacy_projected_constraints\"]=
                num_constraints(m;count_variable_in_set_constraints=true)+4signed
        end
        metrics[\"and_auxiliary_variables\"]=length(and_cache)
        metrics[\"binary_dual_product_cache_entries\"]=length(product_cache)
        metrics[\"model_variables\"]=num_variables(m)
        metrics[\"model_constraints\"]=num_constraints(m;count_variable_in_set_constraints=true)
        metrics[\"expected_model_variables\"]=metrics[\"uncertainty_variables\"]+metrics[\"eta_variables\"]+
            get(metrics,\"dual_multiplier_variables\",0)+get(metrics,\"absolute_value_variables\",0)+
            get(metrics,\"and_aux_variables\",0)+get(metrics,\"binary_dual_product_variables\",0)+
            get(metrics,\"complement_binary_variables\",0)
        metrics[\"variable_count_delta\"]=metrics[\"model_variables\"]-metrics[\"expected_model_variables\"]
        metrics[\"expected_model_constraints\"]=metrics[\"uncertainty_constraints\"]+
            get(metrics,\"eta_bound_constraints\",0)+get(metrics,\"dual_variable_bound_constraints\",0)+
            get(metrics,\"absolute_value_bound_constraints\",0)+get(metrics,\"absolute_value_rows\",0)+
            get(metrics,\"and_binary_domain_constraints\",0)+get(metrics,\"and_linearization_constraints\",0)+
            get(metrics,\"binary_dual_product_constraints\",0)+get(metrics,\"complement_binary_domain_constraints\",0)+
            get(metrics,\"complement_constraints\",0)+get(metrics,\"indicator_constraints\",0)+
            get(metrics,\"stationarity_rows\",0)+get(metrics,\"column_link_rows\",0)+
            get(metrics,\"l1_normalization_rows\",0)
        metrics[\"constraint_count_delta\"]=metrics[\"model_constraints\"]-metrics[\"expected_model_constraints\"]

        constraint_types=Dict{Tuple{String,String},Int}()
        type_listing_includes_variable_sets=1
        try
            for (F,S) in list_of_constraint_types(m;include_variable_in_set_constraints=true)
                key=(string(F),string(S))
                constraint_types[key]=num_constraints(m,F,S)
            end
        catch
            empty!(constraint_types)
            type_listing_includes_variable_sets=0
            for (F,S) in list_of_constraint_types(m)
                key=(string(F),string(S))
                constraint_types[key]=num_constraints(m,F,S)
            end
        end
        metrics[\"constraint_type_listing_includes_variable_sets\"]=type_listing_includes_variable_sets
        metrics[\"constraint_type_count_delta\"]=metrics[\"model_constraints\"]-sum(values(constraint_types))
        return (;model=m,extract=extract,metrics=metrics,primal_set_types=primal_set_types,
            constraint_types=constraint_types,z=z,and_cache=and_cache,
            and_cache_entries=length(and_cache),product_cache_entries=length(product_cache))
    end
end


# FIX10: diagnostic only. Checks the exact zero assignment against every JuMP
# constraint, then measures the continuous LP relaxation of the same Farkas
# master. No production function and no original constraint is changed.
@eval REVCSCertifiedCore begin
    function farkas_audit_zero_assignment(model;tol=1e-8)
        total=0
        violated=0
        maximum=0.0
        for cref in all_constraints(model;include_variable_in_set_constraints=true)
            obj=constraint_object(cref)
            f=obj.func
            f0=if f isa VariableRef
                0.0
            elseif f isa GenericAffExpr
                Float64(f.constant)
            else
                error(\"FIX10_UNSUPPORTED_CONSTRAINT_FUNCTION \$(typeof(f))\")
            end
            set=obj.set
            violation=if set isa MOI.LessThan
                max(0.0,f0-Float64(set.upper))
            elseif set isa MOI.GreaterThan
                max(0.0,Float64(set.lower)-f0)
            elseif set isa MOI.EqualTo
                abs(f0-Float64(set.value))
            elseif set isa MOI.Interval
                max(0.0,Float64(set.lower)-f0,f0-Float64(set.upper))
            elseif set isa MOI.ZeroOne || set isa MOI.Integer || set isa MOI.Reals
                0.0 # Value zero belongs to each of these scalar domains.
            else
                error(\"FIX10_UNSUPPORTED_CONSTRAINT_SET \$(typeof(set))\")
            end
            isfinite(violation) || error(\"FIX10_NONFINITE_ZERO_POINT_VIOLATION\")
            total+=1
            violated+=violation>tol
            maximum=max(maximum,violation)
        end
        counted=num_constraints(model;count_variable_in_set_constraints=true)
        total==counted || error(\"FIX10_ZERO_AUDIT_INCOMPLETE checked=\$total expected=\$counted\")
        return (;checked_constraints=total,violated_constraints=violated,
            maximum_violation=maximum,tolerance=tol,all_zero_feasible=violated==0,
            assignment=\"every_primal_Farkas_master_variable_equals_zero\",
            oracle_certified=false)
    end

    # relax_integrality returns an undo closure in JuMP. The undo is executed
    # unconditionally, even if the LP solve throws, and exact discrete/row
    # counts are checked before permitting the original MIP solve.
    function farkas_audit_root_lp!(model;seconds::Float64=90.0,tol::Float64=1e-6)
        before_vars=num_variables(model)
        before_cons=num_constraints(model;count_variable_in_set_constraints=true)
        discrete=filter(v->is_binary(v)||is_integer(v),all_variables(model))
        original_discrete=length(discrete)
        original_discrete>0 || error(\"FIX10_NO_DISCRETE_VARIABLES\")
        binary_count=count(is_binary,discrete)
        integer_count=original_discrete-binary_count
        undo=relax_integrality(model)
        lp_result=nothing
        try
            sum(is_binary(v)||is_integer(v) for v in discrete)==0 ||
                error(\"FIX10_INTEGRALITY_RESTRICTION_REMAINS\")
            set_time_limit_sec(model,seconds)
            began=time()
            optimize!(model)
            elapsed=time()-began
            term=termination_status(model)
            prim=primal_status(model)
            dual=dual_status(model)
            feasible=has_values(model) && prim==MOI.FEASIBLE_POINT
            obj=feasible ? objective_value(model) : NaN
            bound=try objective_bound(model) catch; NaN end
            maximum_fractionality=0.0
            fractional_count=0
            if feasible
                for v in discrete
                    a=value(v)
                    isfinite(a) || error(\"FIX10_NONFINITE_LP_RELAXATION_VARIABLE\")
                    gap=abs(a-round(a))
                    maximum_fractionality=max(maximum_fractionality,gap)
                    fractional_count+=gap>tol
                end
            end
            lp_result=(;termination_status=string(term),primal_status=string(prim),
                dual_status=string(dual),feasible_point=feasible,objective_value=obj,
                objective_bound=bound,solve_seconds=elapsed,solve_limit_seconds=seconds,
                discrete_variables_original=original_discrete,binary_variables_original=binary_count,
                integer_variables_original=integer_count,lp_fractional_count=feasible ? fractional_count : -1,
                lp_max_integrality_deviation=feasible ? maximum_fractionality : NaN,
                lp_relaxation_integrality_removed=true,
                feasible_mip_incumbent_from_lp=false,oracle_certified=false)
        finally
            undo()
        end
        restored_vars=num_variables(model)
        restored_cons=num_constraints(model;count_variable_in_set_constraints=true)
        restored_discrete=count(v->is_binary(v)||is_integer(v),discrete)
        restored_vars==before_vars && restored_cons==before_cons &&
            restored_discrete==original_discrete ||
            error(\"FIX10_RESTORE_MISMATCH vars=\$restored_vars/\$before_vars constraints=\$restored_cons/\$before_cons discrete=\$restored_discrete/\$original_discrete\")
        # For each solve the existing time limit is preserved; the mode as a
        # whole is independently bounded by OverallSeconds in the Runner.
        set_time_limit_sec(model,seconds)
        return lp_result,(;model_variables=restored_vars,model_constraints=restored_cons,
            restored_discrete_variables=restored_discrete,original_discrete_variables=original_discrete,
            exactly_restored=true,oracle_certified=false)
    end
end


# FIX11: MIP start probing and independent incumbent audit, diagnostic-only.
# A JuMP start value is NOT evidence that HiGHS accepted the start.
@eval REVCSCertifiedCore begin
    function farkas_audit_start_zero!(model;tol::Float64=1e-8)
        zero=farkas_audit_zero_assignment(model;tol=tol)
        zero.all_zero_feasible || error(\"FIX11_ZERO_START_NOT_FEASIBLE\")
        original_obj=objective_function(model)
        zero_obj=if original_obj isa VariableRef
            0.0
        elseif original_obj isa GenericAffExpr
            Float64(original_obj.constant)
        else
            error(\"FIX11_UNSUPPORTED_OBJECTIVE_TYPE \$(typeof(original_obj))\")
        end
        isfinite(zero_obj) && abs(zero_obj)<=tol || error(\"FIX11_ZERO_OBJECTIVE_NOT_ZERO\")
        vars=all_variables(model)
        before_cons=num_constraints(model;count_variable_in_set_constraints=true)
        before_vars=num_variables(model)
        discrete=count(v->is_binary(v)||is_integer(v),vars)
        discrete>0 || error(\"FIX11_NO_DISCRETE_VARIABLES\")
        # Query the *actual solver interface*, never only JuMP's caching layer.
        support=false
        probe_status=\"NOT_CHECKED\"
        probe_error=\"\"
        try
            opt=HiGHS.Optimizer()
            support=MOI.supports(opt,MOI.VariablePrimalStart(),MOI.VariableIndex)
            probe_status=support ? \"SUPPORTED\" : \"UNSUPPORTED\"
        catch e
            probe_status=\"PROBE_ERROR\"
            probe_error=replace(sprint(showerror,e), r\"[\\r\\n,]\"=>\" \")
        end
        provided=0
        verified=0
        if support
            # Set start on every variable (including continuous auxiliary variables).
            # If the underlying solver rejects it, fail closed rather than run
            # a partially specified warm-start experiment.
            for v in vars
                set_start_value(v,0.0)
                provided+=1
            end
            for v in vars
                val=start_value(v)
                (val !== nothing && isfinite(val) && abs(val)<=tol) ||
                    error(\"FIX11_START_READBACK_MISMATCH index=\$(index(v).value)\")
                verified+=1
            end
        end
        num_variables(model)==before_vars &&
          num_constraints(model;count_variable_in_set_constraints=true)==before_cons ||
            error(\"FIX11_START_ALTERED_MODEL\")
        # Never equate write/read-back with solver consumption.
        return (;start_probe=probe_status,probe_error=probe_error,
            solver_interface_support=support,start_submission_attempted=support,
            start_values_submitted=provided,start_values_readback=verified,
            total_variables=before_vars,discrete_variables=discrete,
            zero_constraints_checked=zero.checked_constraints,
            zero_constraints_violated=zero.violated_constraints,
            zero_objective_value=zero_obj,start_value_expected=0.0,
            solver_start_acceptance=\"UNVERIFIED\",
            experiment_class=support ? \"SEEDED_MIP_ATTEMPT\" : \"UNSEEDED_FALLBACK\",
            no_model_modification=true,oracle_certified=false)
    end

    function farkas_audit_mip_incumbent(model;tol::Float64=1e-5)
        term=termination_status(model)
        ps=primal_status(model)
        reported=has_values(model) && ps==MOI.FEASIBLE_POINT
        if !reported
            return (;termination_status=string(term),primal_status=string(ps),
                solver_reported_incumbent=false,independent_incumbent_validated=false,
                constraints_checked=0,violated_constraints=0,
                maximum_constraint_violation=NaN,integrality_violations=0,
                incumbent_objective=NaN,tolerance=tol,
                solver_start_acceptance=\"UNVERIFIED\",oracle_certified=false)
        end
        checked=0;violated=0;max_violation=0.0;integrality_bad=0
        for cref in all_constraints(model;include_variable_in_set_constraints=true)
            obj=constraint_object(cref)
            f=obj.func
            v=if f isa VariableRef
                Float64(value(f))
            elseif f isa GenericAffExpr
                Float64(value(f))
            else
                error(\"FIX11_UNSUPPORTED_INCUMBENT_CONSTRAINT_FUNCTION \$(typeof(f))\")
            end
            isfinite(v) || error(\"FIX11_NONFINITE_INCUMBENT_VALUE\")
            set=obj.set
            violation=if set isa MOI.LessThan
                max(0.0,v-Float64(set.upper))
            elseif set isa MOI.GreaterThan
                max(0.0,Float64(set.lower)-v)
            elseif set isa MOI.EqualTo
                abs(v-Float64(set.value))
            elseif set isa MOI.Interval
                max(0.0,Float64(set.lower)-v,v-Float64(set.upper))
            elseif set isa MOI.ZeroOne
                max(0.0,-v,v-1.0,abs(v-round(v)))
            elseif set isa MOI.Integer
                abs(v-round(v))
            elseif set isa MOI.Reals
                0.0
            else
                error(\"FIX11_UNSUPPORTED_INCUMBENT_CONSTRAINT_SET \$(typeof(set))\")
            end
            checked+=1
            if violation>tol
                violated+=1
                if set isa MOI.ZeroOne || set isa MOI.Integer
                    integrality_bad+=1
                end
            end
            max_violation=max(max_violation,violation)
        end
        checked==num_constraints(model;count_variable_in_set_constraints=true) ||
            error(\"FIX11_INCUMBENT_AUDIT_INCOMPLETE\")
        return (;termination_status=string(term),primal_status=string(ps),
            solver_reported_incumbent=true,independent_incumbent_validated=violated==0,
            constraints_checked=checked,violated_constraints=violated,
            maximum_constraint_violation=max_violation,
            integrality_violations=integrality_bad,
            incumbent_objective=objective_value(model),tolerance=tol,
            solver_start_acceptance=\"UNVERIFIED\",oracle_certified=false)
    end
end


# FIX12: a fixed FULL-DOMAIN uncertainty realization yields an exact LP
# subproblem. No production C&CG function, physical constraint, or dataset is
# touched. Positive outcomes are NUMERICALLY checked candidates, not certified
# full-domain Farkas oracles.
@eval REVCSCertifiedCore begin
    function farkas_fixed_pattern_values(z, and_cache; pattern::String=\"all-plus\")
        pattern in (\"all-plus\",\"all-minus\",\"nominal\") ||
            error(\"FIX12_INVALID_WITNESS_PATTERN\")
        iseven(length(z)) && !isempty(z) || error(\"FIX12_UNPAIRED_UNCERTAINTY_BITS\")
        vals=zeros(Float64,length(z))
        for j in 1:2:length(z)
            if pattern==\"all-plus\"
                vals[j]=1.0
            elseif pattern==\"all-minus\"
                vals[j+1]=1.0
            end
            vals[j]+vals[j+1]<=1.0 || error(\"FIX12_INVALID_THREE_STATE_COORDINATE\")
        end
        assignments=Dict{VariableRef,Float64}()
        for (v,x) in zip(z,vals)
            is_binary(v) || error(\"FIX12_UNCERTAINTY_VARIABLE_NOT_BINARY\")
            assignments[v]=x
        end
        for (key,v) in and_cache
            length(key)==2 || error(\"FIX12_NONQUADRATIC_AND_KEY\")
            a=Int(key[1]);b=Int(key[2])
            1<=a<=length(z) && 1<=b<=length(z) ||
                error(\"FIX12_AND_KEY_OUTSIDE_FULL_DOMAIN\")
            is_binary(v) || error(\"FIX12_AND_AUX_NOT_BINARY\")
            haskey(assignments,v) && error(\"FIX12_DUPLICATE_BINARY_VARIABLE\")
            assignments[v]=vals[a]*vals[b]
        end
        return assignments,(;
            pattern,uncertainty_coordinates=div(length(z),2),
            uncertainty_binary_variables=length(z),
            and_auxiliary_binary_variables=length(and_cache),
            active_plus_coordinates=count(==(1.0),vals[1:2:end]),
            active_minus_coordinates=count(==(1.0),vals[2:2:end]),
            full_domain_three_state_feasible=true)
    end

    function farkas_fixed_pattern_lp!(audited; pattern::String=\"all-plus\",
            seconds::Float64=90.0, audit_tol::Float64=1e-7,
            witness_path::String=\"\")
        m=audited.model
        assignments,layout=farkas_fixed_pattern_values(audited.z,audited.and_cache;pattern)
        discrete=filter(v->is_binary(v)||is_integer(v),all_variables(m))
        isempty(discrete) && error(\"FIX12_NO_DISCRETE_VARIABLES\")
        length(discrete)==length(assignments) ||
            error(\"FIX12_UNACCOUNTED_DISCRETE_VARIABLES \$(length(discrete)) != \$(length(assignments))\")
        all(v->is_binary(v) && haskey(assignments,v),discrete) ||
            error(\"FIX12_DISCRETE_VARIABLE_LAYOUT_CHANGED\")
        old_vars=num_variables(m)
        old_constraints=num_constraints(m;count_variable_in_set_constraints=true)
        # Fix every original binary by an explicit linear equality. All AND
        # binaries are fixed to products of their two uncertainty bits.
        for v in discrete
            @constraint(m,v==assignments[v])
        end
        fixed_row_count=num_constraints(m;count_variable_in_set_constraints=true)-old_constraints
        fixed_row_count==length(discrete) || error(\"FIX12_BINARY_FIX_ROW_COUNT_MISMATCH\")
        num_variables(m)==old_vars || error(\"FIX12_FIX_ADDED_VARIABLES\")
        undo=relax_integrality(m)
        result=nothing
        try
            all(v->!is_binary(v) && !is_integer(v),discrete) ||
                error(\"FIX12_RELAXED_MODEL_STILL_DISCRETE\")
            set_time_limit_sec(m,seconds)
            elapsed=@elapsed optimize!(m)
            term=termination_status(m)
            ps=primal_status(m)
            feasible=has_values(m) && ps==MOI.FEASIBLE_POINT
            lp_value=feasible ? Float64(objective_value(m)) : NaN
            lp_bound=try Float64(objective_bound(m)) catch; NaN end
            audit=feasible ? farkas_audit_mip_incumbent(m;tol=audit_tol) : nothing
            binaries_valid=false;max_binary_error=NaN
            objective_value_agrees=false
            if feasible
                max_binary_error=maximum(abs(value(v)-assignments[v]) for v in discrete)
                binaries_valid=isfinite(max_binary_error) && max_binary_error<=audit_tol
                objective_expression=Float64(value(objective_function(m)))
                objective_value_agrees=isfinite(objective_expression) &&
                    abs(objective_expression-lp_value)<=audit_tol*max(1.0,abs(lp_value))
            end
            audited_all=feasible && audit!==nothing &&
                audit.independent_incumbent_validated &&
                audit.violated_constraints==0 && binaries_valid && objective_value_agrees
            # A tolerance-aware margin is required; we do not call a tiny
            # positive floating result a violation of the 1e-8 Farkas gate.
            required_margin=max(1e-8,100.0*audit_tol)
            candidate=audited_all && isfinite(lp_value) && lp_value>required_margin
            if candidate && !isempty(witness_path)
                open(witness_path,\"w\") do io
                    println(io,\"variable_index\\tvalue\")
                    for v in all_variables(m)
                        println(io,index(v).value,'\\t',repr(Float64(value(v))))
                    end
                end
            end
            interpretation=candidate ? \"NUMERIC_POSITIVE_WITNESS_FIXED_PATTERN\" :
                (term==MOI.OPTIMAL && audited_all ?
                    \"NO_POSITIVE_WITNESS_FOR_SELECTED_PATTERN\" :
                    \"UNRESOLVED_FIXED_PATTERN_LP\")
            result=(;pattern,termination_status=string(term),primal_status=string(ps),
                objective_value=lp_value,objective_bound=lp_bound,solve_seconds=elapsed,
                seconds_per_solve=seconds,solver=\"HiGHS.Optimizer\",presolve=\"on\",
                original_variables=old_vars,original_constraints=old_constraints,
                fixed_binary_variables=length(discrete),additional_fixed_rows=fixed_row_count,
                full_domain_uncertainty_bits=layout.uncertainty_binary_variables,
                and_auxiliary_bits=layout.and_auxiliary_binary_variables,
                active_plus_coordinates=layout.active_plus_coordinates,
                active_minus_coordinates=layout.active_minus_coordinates,
                uncertainty_coordinates=layout.uncertainty_coordinates,
                fixed_pattern_full_domain_feasible=layout.full_domain_three_state_feasible,
                lp_integrality_relaxed_after_binary_fix=true,
                solver_reported_feasible=feasible,
                numerically_validated=audited_all,
                checked_constraints=feasible ? audit.constraints_checked : 0,
                violated_constraints=feasible ? audit.violated_constraints : -1,
                maximum_constraint_violation=feasible ? audit.maximum_constraint_violation : NaN,
                max_original_binary_deviation=max_binary_error,
                original_binary_integrality_valid=binaries_valid,
                independent_objective_check=objective_value_agrees,
                numerical_validation_tolerance=audit_tol,
                required_positive_margin=required_margin,
                positive_candidate=candidate,interpretation,
                witness_vector_saved=candidate && !isempty(witness_path),
                fixed_pattern_only=true,full_domain_farkas_certified=false,
                full_phi3_oracle_certified=false)
        finally
            # Diagnostic-only model; restore integrality even on exceptions.
            undo()
        end
        return result
    end
end
""")
    resource20("REVCS19_G7_4_2_FIX14_CERTIFICATE.jl","b6ae503c11c33e9be0559af7889365f21c11f2a78fd2f1d2a35f7cc2c848a164","""# FIX14: diagnostic, non-certifying primal infeasibility ray replay.
# This file does not alter the production model or native C&CG.
# A ray passes only when every linear constraint (including variable bounds)
# can be enumerated and its multipliers pass sign, stationarity and margin checks.

function g742_fix14_ray_audit(m; tolerance::Float64=1e-8, rayfile::String=\"\")
    term=termination_status(m)
    ds=dual_status(m)
    nvars=num_variables(m)
    nrows=num_constraints(m;count_variable_in_set_constraints=true)
    function unresolved(why; checked=0, nonzero=0, mass=0.0, residual=NaN,
                        signres=NaN, margin=NaN)
        return (;status=why,termination=string(term),dual_status=string(ds),
            original_variables=nvars,expected_constraints=nrows,
            inspected_constraints=checked,nonzero_dual_multipliers=nonzero,
            dual_l1_norm=mass,normalized_stationarity_residual=residual,
            normalized_sign_violation=signres,normalized_farkas_margin=margin,
            normalization=\"dual_L1_one\",certificate_numerically_validated=false,
            saved_ray=false,full_phi3_certified=false)
    end
    if term != MOI.INFEASIBLE || ds != MOI.INFEASIBILITY_CERTIFICATE
        return unresolved(\"UNRESOLVED_NO_PRIMAL_INFEASIBILITY_CERTIFICATE\")
    end
    vars=all_variables(m)
    maxindex=maximum((index(v).value for v in vars);init=0)
    stationary=zeros(Float64,maxindex)
    allrows=all_constraints(m;include_variable_in_set_constraints=true)
    length(allrows)==nrows || return unresolved(\"UNRESOLVED_CONSTRAINT_ENUMERATION_MISMATCH\";
                                               checked=length(allrows))
    dualdata=Vector{Tuple{Int,String,Float64,Float64}}()
    total=0.0
    mass=0.0
    badsign=0.0
    nnz=0
    for (i,cref) in enumerate(allrows)
        # A failed dual query must never be converted into an artificial zero.
        y=Float64(dual(cref))
        isfinite(y) || return unresolved(\"UNRESOLVED_NONFINITE_DUAL\";checked=i-1)
        obj=constraint_object(cref)
        f=obj.func
        set=obj.set
        b=0.0
        if set isa MOI.LessThan
            badsign=max(badsign,max(y,0.0))
            b=Float64(set.upper)
        elseif set isa MOI.GreaterThan
            badsign=max(badsign,max(-y,0.0))
            b=Float64(set.lower)
        elseif set isa MOI.EqualTo
            b=Float64(set.value)
        elseif set isa MOI.Interval
            # For interval rows the sign of the multiplier determines
            # which face contributes to the certificate objective.
            b=y>=0 ? Float64(set.lower) : Float64(set.upper)
        else
            return unresolved(\"UNRESOLVED_UNSUPPORTED_CONSTRAINT_SET\";checked=i-1)
        end
        offset=0.0
        if f isa VariableRef
            stationary[index(f).value]+=y
        elseif f isa JuMP.GenericAffExpr
            offset=Float64(f.constant)
            for (v,a) in f.terms
                stationary[index(v).value]+=y*Float64(a)
            end
        elseif f isa Number
            offset=Float64(f)
        else
            return unresolved(\"UNRESOLVED_NONLINEAR_OR_UNSUPPORTED_ROW\";checked=i-1)
        end
        isfinite(offset) && isfinite(b) ||
            return unresolved(\"UNRESOLVED_NONFINITE_CONSTRAINT_DATA\";checked=i-1)
        total+=(b-offset)*y
        mass+=abs(y)
        nnz+=Int(y!=0.0)
        push!(dualdata,(i,string(typeof(set)),y,b-offset))
    end
    mass>0 && isfinite(mass) && isfinite(total) ||
        return unresolved(\"UNRESOLVED_ZERO_OR_NONFINITE_DUAL_RAY\";
            checked=nrows,nonzero=nnz,mass=mass)
    maxstat=maximum(abs,stationary;init=0.0)/mass
    signres=badsign/mass
    margin=total/mass
    ok=isfinite(maxstat) && isfinite(signres) && isfinite(margin) &&
       maxstat<=tolerance && signres<=tolerance && margin>tolerance
    if ok && !isempty(rayfile)
        open(rayfile,\"w\") do io
            println(io,\"constraint_ordinal\\tset_type\\tdual_multiplier_normalized\\trhs_adjusted\")
            for (i,kind,y,rhs) in dualdata
                println(io,i,'\\t',kind,'\\t',repr(y/mass),'\\t',repr(rhs))
            end
        end
    end
    return (;status=ok ? \"VALIDATED_NUMERIC_PRIMAL_RAY\" : \"UNRESOLVED_NUMERIC_RAY_RESIDUAL\",
        termination=string(term),dual_status=string(ds),
        original_variables=nvars,expected_constraints=nrows,
        inspected_constraints=nrows,nonzero_dual_multipliers=nnz,
        dual_l1_norm=mass,normalized_stationarity_residual=maxstat,
        normalized_sign_violation=signres,normalized_farkas_margin=margin,
        normalization=\"dual_L1_one\",certificate_numerically_validated=ok,
        saved_ray=(ok && !isempty(rayfile)),full_phi3_certified=false)
end

function g742_fix14_unavailable_certificate(m,err)
    return (;status=\"UNRESOLVED_CERTIFICATE_EXTRACTION_ERROR\",
        termination=string(termination_status(m)),dual_status=string(dual_status(m)),
        original_variables=num_variables(m),
        expected_constraints=num_constraints(m;count_variable_in_set_constraints=true),
        inspected_constraints=0,nonzero_dual_multipliers=0,dual_l1_norm=NaN,
        normalized_stationarity_residual=NaN,normalized_sign_violation=NaN,
        normalized_farkas_margin=NaN,normalization=\"dual_L1_one\",
        certificate_numerically_validated=false,saved_ray=false,
        full_phi3_certified=false)
end

# This is explicitly a *scope* check, not the creation of a production cut.
# A full response pattern being infeasible for one uncertainty realization
# cannot justify excluding all other recourse patterns or root policies.
function g742_fix14_cut_scope(o,integer_pattern,all_binary::Bool,ray,positive)
    src=read(G742_SOURCE,String)
    extracts=occursin(\"candidate=extract_f()\",src)
    repeats=occursin(\"if gate==:witness\",src) &&
            occursin(\"push!(history,(;iteration,lower,upper,master_complete=false,columns=length(columns),phase=:feasibility))\",src) &&
            occursin(\"continue\",src)
    extracts && repeats || error(\"FIX14_FROZEN_CCG_WITNESS_ROUTING_NOT_VERIFIED\")
    binary_values=all(k->k in (0,1),integer_pattern.values)
    # For a *binary-only* pattern, the conditional Hamming cut is >=1
    # for any distinct binary vector, and equals zero at this one vector.
    # It is NOT inserted in the real C&CG; a feasible recourse pattern
    # for another uncertainty must never be globally excluded.
    scoped=(all_binary && binary_values && positive &&
            ray.certificate_numerically_validated)
    return (;branch=o.branch,uncertainty_pattern=o.witness_pattern,
        response_pattern_variables=length(integer_pattern.values),
        all_response_variables_binary=all_binary,
        observed_pattern_values_zero_one=binary_values,
        conditional_hamming_identity_checked=(all_binary && binary_values),
        scoped_infeasibility_certificate_validated=scoped,
        exact_scenario_only=true,exact_fixed_predecessor_only=true,
        exact_response_pattern_only=true,other_response_patterns_excluded=false,
        global_feasibility_cut_validated=false,
        production_root_cut_authorized=false,
        production_source_unchanged=true,
        native_ccg_transfers_adversarial_scenario=extracts && repeats,
        proposed_action=\"DIAGNOSTIC_ONLY_NO_CUT_ADDED\",
        full_phi3_certified=false)
end
""")
    resource20("REVCS19_G7_4_2_FIX15_1_CSV_PARSER.jl","cf7b99db0439499fa249553edbf429ac469e85a3f00d6aef2ae00f1876b460ae","""# FIX15.1 — strict, dependency-free RFC 4180-style CSV record parser.
# Handles quoted commas, escaped double quotes, empty cells, CRLF and quoted newlines.
# Rejects malformed quotes rather than silently changing archived evidence.
function g742_csv_records(bytes::Vector{UInt8})
    records=Vector{Vector{String}}()
    fields=String[]
    field=IOBuffer()
    in_quotes=false
    closed_quote=false
    at_field_start=true
    n=length(bytes)
    i=(n>=3 && bytes[1]==0xef && bytes[2]==0xbb && bytes[3]==0xbf) ? 4 : 1
    while i<=n
        c=bytes[i]
        if in_quotes
            if c==0x22
                if i<n && bytes[i+1]==0x22
                    write(field,UInt8(0x22))
                    i+=1
                else
                    in_quotes=false
                    closed_quote=true
                end
            else
                write(field,c)
            end
        elseif c==0x2c || c==0x0a || c==0x0d
            push!(fields,String(take!(field)))
            at_field_start=true
            closed_quote=false
            if c==0x0a || c==0x0d
                push!(records,fields)
                fields=String[]
                if c==0x0d && i<n && bytes[i+1]==0x0a
                    i+=1
                end
            end
        elseif closed_quote
            error(\"CSV_FORMAT_ERROR: unexpected character after closing quote\")
        elseif c==0x22
            at_field_start || error(\"CSV_FORMAT_ERROR: unexpected quote in unquoted field\")
            in_quotes=true
            at_field_start=false
        else
            write(field,c)
            at_field_start=false
        end
        i+=1
    end
    in_quotes && error(\"CSV_FORMAT_ERROR: unterminated quoted field\")
    if !isempty(fields) || !at_field_start || closed_quote
        push!(fields,String(take!(field)))
        push!(records,fields)
    end
    return records
end

function g742_csvone(file)
    records=g742_csv_records(read(file))
    length(records)==2 || error(\"Expected exactly one CSV data row: \$file\")
    names,values=records
    length(names)==length(values) || error(\"Malformed CSV row: \$file\")
    !isempty(names) && all(x->!isempty(x),names) && length(unique(names))==length(names) ||
        error(\"Malformed or duplicate CSV header: \$file\")
    return Dict{String,String}(k=>v for (k,v) in zip(names,values))
end

function g742_fix15_1_csv_selftest(evidence_dir::AbstractString)
    # Embedded comma, escaped quote, empty value, CRLF, UTF-8 and embedded newline.
    test1=\"a,b,c\\r\\n\\\"alpha, beta\\\",\\\"he said \\\"\\\"hello\\\"\\\"\\\",\\\"\\\"\\r\\n\"
    g742_csv_records(collect(codeunits(test1)))==
        [[\"a\",\"b\",\"c\"],[\"alpha, beta\",\"he said \\\"hello\\\"\",\"\"]] ||
        error(\"FIX15_1_CSV_ESCAPED_QUOTE_TEST_FAILED\")
    test2=\"key,value\\n\\\"line one\\nline two\\\",\\\"μ,Ω\\\"\\n\"
    g742_csv_records(collect(codeunits(test2)))==
        [[\"key\",\"value\"],[\"line one\\nline two\",\"μ,Ω\"]] ||
        error(\"FIX15_1_CSV_MULTILINE_UTF8_TEST_FAILED\")
    test3=UInt8[0xef,0xbb,0xbf]
    append!(test3,collect(codeunits(\"id,value\\r\\n7,\\r\\n\")))
    g742_csv_records(test3)==[[\"id\",\"value\"],[\"7\",\"\"]] ||
        error(\"FIX15_1_CSV_BOM_EMPTY_TEST_FAILED\")
    for bad in (\"a,b\\n\\\"unterminated,b\\n\", \"a,b\\ninvalid\\\"quote,2\\n\", \"a,b\\n\\\"ok\\\"junk,2\\n\")
        caught=false
        try
            g742_csv_records(collect(codeunits(bad)))
        catch
            caught=true
        end
        caught || error(\"FIX15_1_CSV_INVALID_QUOTE_ACCEPTED\")
    end
    files=(\"FIX13_CROSSCHECK.csv\",\"FIX13_SCENARIO_IDENTITY.csv\",
        \"FIX13_PRIMAL_LP_STATUS.csv\",\"FIX14_PRIMAL_CERTIFICATE_AUDIT.csv\",
        \"FIX14_FEASIBILITY_CUT_SCOPE.csv\",\"FARKAS_FIXED_PATTERN_LP.csv\",
        \"PHI3_DOMAIN_PREFLIGHT.csv\",\"RUNNER_SUMMARY.csv\")
    for name in files
        row=g742_csvone(joinpath(evidence_dir,name))
        !isempty(row) || error(\"FIX15_1_ARCHIVED_CSV_EMPTY: \$name\")
    end
    domain=g742_csvone(joinpath(evidence_dir,\"PHI3_DOMAIN_PREFLIGHT.csv\"))
    length(domain)==17 && haskey(domain,\"domain_scope\") && occursin(\",\",domain[\"domain_scope\"]) ||
        error(\"FIX15_1_ARCHIVED_SCOPE_CSV_WIDTH_OR_VALUE_INVALID\")
    println(\"G742_FIX15_1_CSV_TEST=PASS archived_csv=8 domain_columns=17\")
    flush(stdout)
    return true
end
""")
    resource20("REVCS19_G7_4_2_FIX15_HANDOFF.jl","b921e9b3eaacf093a944f5ce41ca3bbbf6caeab610e50a2794a12ce0d09523e8","""# FIX15: read-only, provenance-anchored witness-to-next-Inner scenario handoff audit.
# It replays the exact documented FIX14 all-plus scenario for its fixed Stage-2
# predecessor, but DOES NOT claim that a production full Farkas master called
# extract_f(), that a native C&CG iteration completed, or that Phi3 is certified.

const G742_FIX15_ARCHIVED_MANIFEST_SHA256 = \"3bb17df900a59805a3b003ca159af08db9a8fbd1f604726c85a897a4f9afc54c\"
const G742_FIX15_EVIDENCE_FILES = (
    \"FIX13_INNER_INTEGER_PATTERN.tsv\", \"FIX13_CROSSCHECK.csv\",
    \"FIX13_SCENARIO_IDENTITY.csv\", \"FIX13_PRIMAL_LP_STATUS.csv\",
    \"FIX14_PRIMAL_CERTIFICATE_AUDIT.csv\", \"FIX14_FEASIBILITY_CUT_SCOPE.csv\",
    \"FARKAS_FIXED_PATTERN_LP.csv\", \"FIX14_PRIMAL_DUAL_RAY.tsv\",
    \"FARKAS_FIXED_PATTERN_WITNESS.tsv\", \"PHI3_DOMAIN_PREFLIGHT.csv\",
    \"RUNNER_SUMMARY.csv\", \"GATE_STATUS.txt\")

function g742_fix15_event(o,phase;detail=\"\")
    msg=\"G742_FIX15 phase=\$phase detail=\$detail\"
    println(msg)
    flush(stdout)
    open(joinpath(o.output,\"FIX15_HANDOFF_EVENTS.tsv\"),\"a\") do io
        println(io,\"\$phase\\t\$detail\")
        flush(io)
    end
end

# Serialize all numeric physical profiles, uncertainty bits and derived ANDs.
# Do not use Dict display order, and ignore the human-readable scenario name.
function g742_fix15_numeric_bytes(s)
    io=IOBuffer()
    for key in sort(collect(keys(s)))
        key==\"name\" && continue
        value=s[key]
        if value isa Number
            println(io,key,\"\\tS\\t\",repr(Float64(value)))
        elseif value isa AbstractArray
            print(io,key,\"\\tA\\t\",join(size(value),\",\"),\"\\t\")
            for x in value
                x isa Number || error(\"FIX15_NONNUMERIC_SCENARIO_COMPONENT: \$key\")
                print(io,repr(Float64(x)),';')
            end
            println(io)
        else
            error(\"FIX15_UNSUPPORTED_SCENARIO_COMPONENT: \$key\")
        end
    end
    return take!(io)
end

function g742_fix15_evidence(o,state_sha,scope)
    o.branch==\"paper_zero\" || error(\"FIX15_EVIDENCE_IS_PAPER_ZERO_ONLY\")
    o.witness_pattern==\"all-plus\" || error(\"FIX15_EVIDENCE_IS_ALL_PLUS_ONLY\")
    manifestfile=joinpath(G742_ROOT,\"FIX15_EVIDENCE_MANIFEST.tsv\")
    bytes2hex(sha256(read(manifestfile)))==G742_FIX15_ARCHIVED_MANIFEST_SHA256 ||
        error(\"FIX15_EVIDENCE_MANIFEST_DRIFT\")
    lines=readlines(manifestfile)
    length(lines)==length(G742_FIX15_EVIDENCE_FILES)+1 && first(lines)==\"sha256\\tfile\" ||
        error(\"FIX15_EVIDENCE_MANIFEST_MALFORMED\")
    recorded=Set{String}()
    for line in lines[2:end]
        cols=split(line,'\\t')
        length(cols)==2 || error(\"FIX15_EVIDENCE_MANIFEST_BAD_ROW\")
        expected,rel=cols
        rel in G742_FIX15_EVIDENCE_FILES && !(rel in recorded) ||
            error(\"FIX15_EVIDENCE_FILE_MISSING_OR_DUPLICATE: \$rel\")
        file=joinpath(G742_ROOT,\"FIX14_EVIDENCE\",rel)
        isfile(file) && bytes2hex(sha256(read(file)))==expected ||
            error(\"FIX15_EVIDENCE_HASH_MISMATCH: \$rel\")
        push!(recorded,rel)
    end
    length(recorded)==length(G742_FIX15_EVIDENCE_FILES) || error(\"FIX15_EVIDENCE_FILES_INCOMPLETE\")
    evidence_file=k->joinpath(G742_ROOT,\"FIX14_EVIDENCE\",k)
    row=k->g742_csvone(evidence_file(k))
    cross=row(\"FIX13_CROSSCHECK.csv\")
    scenario=row(\"FIX13_SCENARIO_IDENTITY.csv\")
    primal=row(\"FIX13_PRIMAL_LP_STATUS.csv\")
    cert=row(\"FIX14_PRIMAL_CERTIFICATE_AUDIT.csv\")
    cut=row(\"FIX14_FEASIBILITY_CUT_SCOPE.csv\")
    fixed=row(\"FARKAS_FIXED_PATTERN_LP.csv\")
    prior=row(\"PHI3_DOMAIN_PREFLIGHT.csv\")
    runner=row(\"RUNNER_SUMMARY.csv\")
    prior_status=read(evidence_file(\"GATE_STATUS.txt\"),String)
    (occursin(\"GATE_7_4_2_STATUS=PRIMAL_CERTIFICATE_CUT_SCOPE_AUDIT_COMPLETED_NOT_CERTIFIED\",prior_status) &&
     occursin(\"FULL_PHI3_ORACLE_CERTIFIED=NO\",prior_status)) ||
     error(\"FIX15_ARCHIVED_GATE_STATUS_INVALID\")
    runner[\"Branch\"]==\"paper_zero\" && runner[\"Mode\"]==\"farkas-certificate-cut-audit\" &&
        runner[\"ModeEvidenceValid\"]==\"True\" && runner[\"JuliaProcessExit\"]==\"0\" ||
        error(\"FIX15_ARCHIVED_RUNNER_NOT_SUCCESSFUL\")
    prior[\"branch\"]==\"paper_zero\" && prior[\"predecessor_sha256\"]==state_sha &&
        prior[\"physical_source_sha256\"]==G742_REAL_SOURCE_HASH &&
        prior[\"scope\"]==scope && prior[\"stage\"]==\"3\" &&
        prior[\"active_coordinates\"]==\"1882\" && prior[\"binary_indicators\"]==\"3764\" ||
        error(\"FIX15_PREDECESSOR_SOURCE_OR_SCOPE_DRIFT\")
    (scenario[\"pattern\"]==\"all-plus\" && scenario[\"active_coordinates\"]==\"1882\" &&
     scenario[\"plus_coordinates\"]==\"1882\" && scenario[\"minus_coordinates\"]==\"0\" &&
     scenario[\"scenario_validated\"]==\"true\" &&
     scenario[\"physical_source_hash\"]==G742_REAL_SOURCE_HASH &&
     parse(Float64,scenario[\"symbolic_numerical_max_difference\"])<=1e-8) ||
     error(\"FIX15_ARCHIVED_SCENARIO_NOT_VALIDATED\")
    (fixed[\"pattern\"]==\"all-plus\" && fixed[\"positive_candidate\"]==\"true\" &&
     fixed[\"numerically_validated\"]==\"true\" && fixed[\"fixed_pattern_only\"]==\"true\" &&
     parse(Float64,fixed[\"objective_value\"])>1e-5 &&
     fixed[\"full_phi3_oracle_certified\"]==\"false\") ||
     error(\"FIX15_ARCHIVED_FIXED_PATTERN_WITNESS_INVALID\")
    (cross[\"branch\"]==\"paper_zero\" && cross[\"uncertainty_pattern\"]==\"all-plus\" &&
     cross[\"same_run_same_pattern\"]==\"true\" && cross[\"farkas_positive_candidate\"]==\"true\" &&
     cross[\"farkas_numerically_validated\"]==\"true\" &&
     cross[\"primal_farkas_consistent\"]==\"true\" &&
     cross[\"independent_primal_infeasible\"]==\"true\" &&
     cross[\"contradiction_detected\"]==\"false\") ||
     error(\"FIX15_ARCHIVED_CROSSCHECK_INVALID\")
    (primal[\"pattern\"]==\"all-plus\" && primal[\"termination_status\"]==\"INFEASIBLE\" &&
     primal[\"original_integer_values_fixed_exactly\"]==\"true\" &&
     primal[\"remaining_discrete_variables\"]==\"0\") ||
     error(\"FIX15_ARCHIVED_PRIMAL_NOT_INFEASIBLE\")
    (cert[\"status\"]==\"VALIDATED_NUMERIC_PRIMAL_RAY\" &&
     cert[\"certificate_numerically_validated\"]==\"true\" &&
     parse(Float64,cert[\"normalized_farkas_margin\"])>1e-8 &&
     parse(Float64,cert[\"normalized_stationarity_residual\"])<=1e-8 &&
     parse(Float64,cert[\"normalized_sign_violation\"])<=1e-8) ||
     error(\"FIX15_ARCHIVED_RAY_NOT_VALIDATED\")
    (cut[\"branch\"]==\"paper_zero\" && cut[\"uncertainty_pattern\"]==\"all-plus\" &&
     cut[\"scoped_infeasibility_certificate_validated\"]==\"true\" &&
     cut[\"exact_scenario_only\"]==\"true\" &&
     cut[\"exact_fixed_predecessor_only\"]==\"true\" &&
     cut[\"exact_response_pattern_only\"]==\"true\" &&
     cut[\"other_response_patterns_excluded\"]==\"false\" &&
     cut[\"global_feasibility_cut_validated\"]==\"false\" &&
     cut[\"production_root_cut_authorized\"]==\"false\" &&
     cut[\"native_ccg_transfers_adversarial_scenario\"]==\"true\") ||
     error(\"FIX15_ARCHIVED_CUT_SCOPE_INVALID\")
    patfile=evidence_file(\"FIX13_INNER_INTEGER_PATTERN.tsv\")
    phash=bytes2hex(sha256(read(patfile)))
    cross[\"inner_pattern_sha256\"]==phash || error(\"FIX15_ARCHIVED_PATTERN_HASH_DRIFT\")
    patlines=readlines(patfile)
    length(patlines)==4181 && patlines[1]==\"variable_index\\tvalue\" ||
        error(\"FIX15_ARCHIVED_INTEGER_PATTERN_SHAPE_INVALID\")
    ix=Int[];values=Int[]
    for line in patlines[2:end]
        fields=split(line,'\\t')
        length(fields)==2 || error(\"FIX15_PATTERN_ROW_INVALID\")
        push!(ix,parse(Int,fields[1]));push!(values,parse(Int,fields[2]))
    end
    (issorted(ix) && length(unique(ix))==4180 && all(x->x>0,ix) &&
     all(x->x==0 || x==1,values) && cross[\"inner_pattern_variables\"]==\"4180\" &&
     cut[\"response_pattern_variables\"]==\"4180\") ||
     error(\"FIX15_PATTERN_NOT_BINARY_OR_DUPLICATED\")
    source=read(G742_SOURCE,String)
    # Examine the exact native C&CG witness-to-next-iteration branch (static only).
    all_lines=split(source,'\\n')
    first_line=findfirst(x->occursin(\"if gate==:witness\",x),all_lines)
    first_line===nothing && error(\"FIX15_NO_NATIVE_WITNESS_BRANCH\")
    snippet=join(all_lines[first_line:min(length(all_lines),first_line+12)],\"\\n\")
    (occursin(\"candidate=extract_f()\",snippet) &&
     occursin(\"phase=:feasibility\",snippet) &&
     occursin(\"continue\",snippet) &&
     !occursin(\"push!(forbidden\",snippet)) ||
     error(\"FIX15_NATIVE_WITNESS_ROUTE_CHANGED\")
    return (;integer_indices=ix,integer_values=values,pattern_sha256=phash,
        predecessor_sha256=state_sha,archived_witness_objective=parse(Float64,fixed[\"objective_value\"]),
        archived_ray_margin=parse(Float64,cert[\"normalized_farkas_margin\"]),
        source_route_verified=true,source_of_candidate=\"FIX14_VERIFIED_ALL_PLUS_REPLAY_NOT_NATIVE_EXTRACT_F\",
        evidence_manifest_sha256=G742_FIX15_ARCHIVED_MANIFEST_SHA256)
end

function g742_fix15_handoff_audit(o,cfg,grids,st,z0,state_sha,scope)
    isfile(joinpath(o.output,\"FIX15_HANDOFF_EVENTS.tsv\")) && rm(joinpath(o.output,\"FIX15_HANDOFF_EVENTS.tsv\"))
    g742_fix15_event(o,\"START\";detail=\"archived_FIX14_witness_replay;not_native_extracted\")
    o.iters==1 || error(\"FIX15_KEEP_PREVIOUS_MAX_ITERATIONS_1\")
    g742_fix15_1_csv_selftest(joinpath(G742_ROOT,\"FIX14_EVIDENCE\"))
    g742_fix15_event(o,\"CSV_PARSER_VERIFIED\";detail=\"archived_csv=8;domain_columns=17\")
    proof=g742_fix15_evidence(o,state_sha,scope)
    g742_fix15_event(o,\"ARCHIVED_EVIDENCE_VERIFIED\";detail=\"pattern_sha256=\$(proof.pattern_sha256) predecessor_sha256=\$state_sha\")
    candidate,identity=g742_fix13_realization(\"all-plus\")
    validate_scenario(3,candidate)
    identity.active_coordinates==1882 && identity.plus_coordinates==1882 &&
        identity.minus_coordinates==0 &&
        identity.symbolic_numerical_max_difference<=1e-8 ||
        error(\"FIX15_REBUILT_SCENARIO_IDENTITY_MISMATCH\")
    # Before/after byte identity proves there is no silent mutation of the
    # candidate's physical profiles, bit metadata or derived AND terms.
    numeric_before=g742_fix15_numeric_bytes(candidate)
    scenario_hash=bytes2hex(sha256(numeric_before))
    write(joinpath(o.output,\"FIX15_HANDOFF_SCENARIO.tsv\"),numeric_before)
    stbefore=encode_state(st,grids)
    z0before=copy(z0)
    g742_fix15_event(o,\"SCENARIO_QUEUED\";detail=\"source=archived_FIX14 fixed_pattern=all-plus scenario_sha256=\$scenario_hash\")
    write_rows(joinpath(o.output,\"FIX15_EVIDENCE_HANDOFF.csv\"),[(;
        branch=o.branch,stage=3,source_of_candidate=proof.source_of_candidate,
        original_fixed_predecessor_sha256=proof.predecessor_sha256,
        scenario_sha256=scenario_hash,archived_integer_pattern_sha256=proof.pattern_sha256,
        archived_integer_pattern_variables=length(proof.integer_indices),
        original_fixed_pattern_farkas_objective=proof.archived_witness_objective,
        archived_normalized_primal_ray_margin=proof.archived_ray_margin,
        evidence_manifest_sha256=proof.evidence_manifest_sha256,
        source_ccg_witness_branch_verified=proof.source_route_verified,
        actual_native_extract_f_executed=false,full_farkas_master_solved=false,
        global_cut_added=false,other_recourse_patterns_excluded=false,
        full_phi3_certified=false)])
    # Recreate the production `builder` closure, including the same fixed
    # predecessor and all cost/physical settings. No no-good/root cut is added.
    builder=u->first(build_certified_stage(3,st,u,grids;
        direction=:lower,lower_cuts=REVCSCertifiedCore.BinaryCut[],
        seconds=o.seconds,capacity_mode=cfg.capacity_mode,
        initial_station_state=z0))
    g742_fix15_event(o,\"NEXT_INNER_BUILD_START\";detail=\"stage=3;direction=lower;cuts=0\")
    inner=REVCSCertifiedCore.ensure_solver_column!(builder(candidate))
    vars=num_variables(inner)
    cons=num_constraints(inner;count_variable_in_set_constraints=true)
    current_integer=filter(v->is_binary(v)||is_integer(v),all_variables(inner))
    layout=[index(v).value for v in current_integer]
    layout==proof.integer_indices || error(\"FIX15_NEXT_INNER_INTEGER_LAYOUT_MISMATCH\")
    vars==75481 && cons==153238 || error(\"FIX15_NEXT_INNER_MODEL_SIZE_DRIFT\")
    bytes2hex(sha256(g742_fix15_numeric_bytes(candidate)))==scenario_hash ||
        error(\"FIX15_BUILDER_MUTATED_SCENARIO\")
    encode_state(st,grids)==stbefore && z0==z0before ||
        error(\"FIX15_BUILDER_MUTATED_PREDECESSOR\")
    write_rows(joinpath(o.output,\"FIX15_NEXT_INNER_BUILD.csv\"),[(;
        branch=o.branch,source_of_candidate=proof.source_of_candidate,
        scenario_sha256=scenario_hash,predecessor_sha256=state_sha,
        model_variables=vars,model_constraints=cons,
        integer_layout_matches_archived=true,integer_variable_count=length(layout),
        uncertainty_validated=true,scenario_unchanged_during_build=true,
        predecessor_unchanged_during_build=true,lower_cuts=0,root_cuts_added=0,
        other_patterns_excluded=false,source_frozen=true,
        seconds_per_solve=o.seconds,threads=o.threads,outer_relative_gap=o.gap,
        max_iterations=o.iters,full_phi3_certified=false)])
    g742_fix15_event(o,\"NEXT_INNER_BUILD_DONE\";detail=\"vars=\$vars constraints=\$cons integer_layout=\$(length(layout)) scenario_unmodified=true predecessor_unmodified=true\")
    set_time_limit_sec(inner,Float64(o.seconds))
    g742_fix15_event(o,\"NEXT_INNER_SOLVE_START\";detail=\"seconds=\$(o.seconds);threads=\$(o.threads)\")
    empty!(REVCSCertifiedCore.SOLVER_TRACE)
    REVCSCertifiedCore.solve_tracked!(inner;context=\"g742_fix15_replay_next_inner\")
    row=REVCSCertifiedCore.min_bounds(inner)
    termination=string(termination_status(inner))
    primal_status_str=string(primal_status(inner))
    new_pattern_differs=false
    contradiction=false
    if row.feasible
        new_pattern=REVCSCertifiedCore.integer_pattern(inner)
        new_pattern.indices==proof.integer_indices || error(\"FIX15_SOLVED_INTEGER_LAYOUT_DRIFT\")
        new_pattern_differs=(new_pattern.values!=proof.integer_values)
        contradiction=!new_pattern_differs
        open(joinpath(o.output,\"FIX15_NEXT_INNER_INTEGER_PATTERN.tsv\"),\"w\") do io
            println(io,\"variable_index\\tvalue\")
            for (ix,k) in zip(new_pattern.indices,new_pattern.values)
                println(io,ix,'\\t',k)
            end
        end
    end
    write_rows(joinpath(o.output,\"FIX15_INNER_SOLVER_TRACE.csv\"),REVCSCertifiedCore.SOLVER_TRACE)
    write_rows(joinpath(o.output,\"FIX15_NEXT_INNER_REPLAY.csv\"),[(;
        branch=o.branch,uncertainty_pattern=o.witness_pattern,
        scenario_sha256=scenario_hash,predecessor_sha256=state_sha,
        model_source=\"frozen_build_certified_stage\",solver=\"HiGHS.Optimizer\",
        solve_termination=termination,primal_status=primal_status_str,
        feasible_incumbent=row.feasible,inner_lower_bound=row.lower,
        inner_upper_bound=row.upper,
        incumbent_pattern_differs_from_archived= row.feasible ? new_pattern_differs : \"NOT_AVAILABLE\",
        contradiction_detected=contradiction,
        singleton_historical_pattern_only=true,production_native_ccg_iteration_executed=false,
        global_farkas_master_solved=false,global_root_cut_added=false,
        other_recourse_patterns_excluded=false,
        full_phi3_certified=false,full_multistage_certified=false)])
    g742_fix15_event(o,\"NEXT_INNER_SOLVE_DONE\";detail=\"termination=\$termination feasible=\$(row.feasible) alternative_pattern=\$new_pattern_differs contradiction=\$contradiction\")
    contradiction && error(\"FIX15_CONTRADICTION_ARCHIVED_INFEASIBLE_PATTERN_REAPPEARED_FEASIBLE\")
    g742_fix15_event(o,\"COMPLETE\";detail=\"handoff_replay_complete;not_native_extracted;no_root_cut;Phi3_not_certified\")
    return (;status=\"WITNESS_HANDOFF_REPLAY_COMPLETED_NOT_CERTIFIED\",
        branch=o.branch,predecessor_sha256=state_sha,scenario_sha256=scenario_hash,
        replay_completed=true,mode=\"witness-handoff-audit\",
        full_phi3_oracle_certified=false)
end
""")
    resource20("REVCS19_G7_4_2_FIX16_NATIVE_BRANCH.jl","c1bd8ea100d7387d6078893e26bcaa2fd55743a23500b2148a8e007acf4078f5","""# FIX16: exercise the FROZEN solve_native_ccg :witness control-flow branch
# with a diagnostic-only injected symbolic_master. The production Farkas master,
# physical source, data, and C&CG function body remain byte-for-byte unchanged.
# The next-Inner physical builder is replayed separately because the agreed
# MaxIterations=1 budget must remain unchanged.

const G742_FIX16_ARCHIVED_MANIFEST_SHA256 = \"9ae9b3a1b04d0293a1094929a0453c5fdf95bc8910d1c4461860c7312af90061\"
const G742_FIX16_EVIDENCE_FILES = (
    \"FIX15_HANDOFF_EVENTS.tsv\", \"FIX15_HANDOFF_SCENARIO.tsv\",
    \"FIX15_EVIDENCE_HANDOFF.csv\", \"FIX15_NEXT_INNER_BUILD.csv\",
    \"FIX15_INNER_SOLVER_TRACE.csv\", \"FIX15_NEXT_INNER_REPLAY.csv\",
    \"FIX15_NEXT_INNER_INTEGER_PATTERN.tsv\", \"RUNNER_SUMMARY.csv\")

function g742_fix16_event(o, phase; detail=\"\")
    line = \"G742_FIX16 phase=\$(phase) detail=\$(detail)\"
    println(line); flush(stdout)
    open(joinpath(o.output, \"FIX16_NATIVE_EVENTS.tsv\"), \"a\") do io
        println(io, phase, '\\t', detail); flush(io)
    end
    return nothing
end

function g742_fix16_verify_fix15_1(o, state_sha, scope, proof)
    o.branch == \"paper_zero\" || error(\"FIX16_EVIDENCE_PAPER_ZERO_ONLY\")
    o.witness_pattern == \"all-plus\" || error(\"FIX16_EVIDENCE_ALL_PLUS_ONLY\")
    o.iters == 1 || error(\"FIX16_MAX_ITERATIONS_MUST_REMAIN_ONE\")
    dir = joinpath(G742_ROOT, \"FIX15_1_EVIDENCE\")
    manifest = joinpath(dir, \"FIX15_1_EVIDENCE_MANIFEST.tsv\")
    isfile(manifest) || error(\"FIX16_FIX15_1_MANIFEST_MISSING\")
    bytes2hex(sha256(read(manifest))) == G742_FIX16_ARCHIVED_MANIFEST_SHA256 ||
        error(\"FIX16_FIX15_1_MANIFEST_HASH_MISMATCH\")
    lines = readlines(manifest)
    length(lines) == length(G742_FIX16_EVIDENCE_FILES) + 1 && first(lines) == \"sha256\\tfile\" ||
        error(\"FIX16_FIX15_1_MANIFEST_MALFORMED\")
    found = Set{String}()
    for line in lines[2:end]
        f = split(line, '\\t')
        length(f) == 2 || error(\"FIX16_FIX15_1_MANIFEST_ROW_INVALID\")
        expected, rel = f
        rel in G742_FIX16_EVIDENCE_FILES && !(rel in found) ||
            error(\"FIX16_FIX15_1_MANIFEST_DUPLICATE_OR_UNKNOWN_FILE\")
        path = joinpath(dir, rel)
        isfile(path) && bytes2hex(sha256(read(path))) == expected ||
            error(\"FIX16_FIX15_1_EVIDENCE_HASH_MISMATCH: \$rel\")
        push!(found, rel)
    end
    length(found) == length(G742_FIX16_EVIDENCE_FILES) || error(\"FIX16_FIX15_1_EVIDENCE_INCOMPLETE\")
    row = name -> g742_csvone(joinpath(dir, name))
    handoff = row(\"FIX15_EVIDENCE_HANDOFF.csv\")
    build = row(\"FIX15_NEXT_INNER_BUILD.csv\")
    replay = row(\"FIX15_NEXT_INNER_REPLAY.csv\")
    runner = row(\"RUNNER_SUMMARY.csv\")
    scenario_path = joinpath(dir, \"FIX15_HANDOFF_SCENARIO.tsv\")
    original_pattern_path = joinpath(G742_ROOT, \"FIX14_EVIDENCE\", \"FIX13_INNER_INTEGER_PATTERN.tsv\")
    alternative_pattern_path = joinpath(dir, \"FIX15_NEXT_INNER_INTEGER_PATTERN.tsv\")
    scenario_hash = bytes2hex(sha256(read(scenario_path)))
    original_hash = bytes2hex(sha256(read(original_pattern_path)))
    alternative_hash = bytes2hex(sha256(read(alternative_pattern_path)))

    (runner[\"RunnerFix\"] == \"FIX15.1\" && runner[\"Mode\"] == \"witness-handoff-audit\" &&
     runner[\"GateStatus\"] == \"WITNESS_HANDOFF_REPLAY_COMPLETED_NOT_CERTIFIED\" &&
     runner[\"ModeEvidenceValid\"] == \"True\" && runner[\"JuliaProcessExit\"] == \"0\") ||
        error(\"FIX16_FIX15_1_RUNNER_NOT_SUCCESSFUL\")
    (handoff[\"branch\"] == \"paper_zero\" && handoff[\"stage\"] == \"3\" &&
     handoff[\"source_of_candidate\"] == \"FIX14_VERIFIED_ALL_PLUS_REPLAY_NOT_NATIVE_EXTRACT_F\" &&
     handoff[\"original_fixed_predecessor_sha256\"] == state_sha &&
     handoff[\"scenario_sha256\"] == scenario_hash &&
     handoff[\"archived_integer_pattern_sha256\"] == proof.pattern_sha256 &&
     handoff[\"actual_native_extract_f_executed\"] == \"false\" &&
     handoff[\"full_farkas_master_solved\"] == \"false\" &&
     handoff[\"global_cut_added\"] == \"false\" &&
     handoff[\"full_phi3_certified\"] == \"false\") ||
        error(\"FIX16_FIX15_1_HANDOFF_EVIDENCE_INVALID\")
    (build[\"scenario_sha256\"] == scenario_hash && build[\"predecessor_sha256\"] == state_sha &&
     build[\"model_variables\"] == \"75481\" && build[\"model_constraints\"] == \"153238\" &&
     build[\"integer_variable_count\"] == \"4180\" &&
     build[\"integer_layout_matches_archived\"] == \"true\" &&
     build[\"scenario_unchanged_during_build\"] == \"true\" &&
     build[\"predecessor_unchanged_during_build\"] == \"true\" &&
     build[\"lower_cuts\"] == \"0\" && build[\"root_cuts_added\"] == \"0\") ||
        error(\"FIX16_FIX15_1_BUILD_EVIDENCE_INVALID\")
    (replay[\"scenario_sha256\"] == scenario_hash && replay[\"predecessor_sha256\"] == state_sha &&
     replay[\"solve_termination\"] == \"TIME_LIMIT\" && replay[\"primal_status\"] == \"FEASIBLE_POINT\" &&
     replay[\"feasible_incumbent\"] == \"true\" &&
     replay[\"incumbent_pattern_differs_from_archived\"] == \"true\" &&
     replay[\"contradiction_detected\"] == \"false\" &&
     replay[\"production_native_ccg_iteration_executed\"] == \"false\" &&
     replay[\"global_farkas_master_solved\"] == \"false\" &&
     replay[\"global_root_cut_added\"] == \"false\") ||
        error(\"FIX16_FIX15_1_REPLAY_EVIDENCE_INVALID\")

    # The scenario bytes from FIX15.1 must be exactly the current frozen all-plus realization.
    archived_scenario, _ = g742_fix13_realization(\"all-plus\")
    bytes2hex(sha256(g742_fix15_numeric_bytes(archived_scenario))) == scenario_hash ||
        error(\"FIX16_FIX15_1_SCENARIO_BYTES_DIFFER_FROM_FROZEN_REALIZATION\")

    # Recheck the 4,180-bit predecessor and the 4,180-bit alternative pattern.
    function read_pattern(path)
        ls = readlines(path)
        length(ls) == 4181 && first(ls) == \"variable_index\\tvalue\" ||
            error(\"FIX16_PATTERN_SHAPE_INVALID: \$(basename(path))\")
        ix = Int[]; vals = Int[]
        for line in ls[2:end]
            f = split(line, '\\t')
            length(f) == 2 || error(\"FIX16_PATTERN_ROW_INVALID\")
            push!(ix, parse(Int, f[1])); push!(vals, parse(Int, f[2]))
        end
        issorted(ix) && length(unique(ix)) == 4180 && all(x -> x == 0 || x == 1, vals) ||
            error(\"FIX16_PATTERN_NOT_UNIQUE_BINARY\")
        return ix, vals
    end
    original_ix, original_values = read_pattern(original_pattern_path)
    alt_ix, alt_values = read_pattern(alternative_pattern_path)
    original_ix == proof.integer_indices && original_values == proof.integer_values ||
        error(\"FIX16_FIX14_PATTERN_NOT_IDENTICAL_TO_VERIFIED_PROOF\")
    original_ix == alt_ix || error(\"FIX16_FIX15_1_PATTERN_LAYOUT_DRIFT\")
    diff = count(i -> original_values[i] != alt_values[i], eachindex(original_values))
    zero_to_one = count(i -> original_values[i] == 0 && alt_values[i] == 1, eachindex(original_values))
    one_to_zero = count(i -> original_values[i] == 1 && alt_values[i] == 0, eachindex(original_values))
    diff == 419 && zero_to_one == 209 && one_to_zero == 210 ||
        error(\"FIX16_FIX15_1_ALTERNATIVE_PATTERN_DIFF_MISMATCH\")

    return (; scenario_hash, original_hash, alternative_hash,
        original_values, original_indices=original_ix, alternative_values=alt_values,
        predecessor_sha256=state_sha, archived_manifest_sha256=G742_FIX16_ARCHIVED_MANIFEST_SHA256,
        alternative_hamming_distance=diff, zero_to_one, one_to_zero)
end

# Diagnostic-specific callable types select the overload below without replacing
# the generic production symbolic_master method used by real C&CG calls.
@eval REVCSCertifiedCore begin
    struct FIX16InjectedUncertaintyFactory end
    struct FIX16InjectedSymbolicBuilder end
    mutable struct FIX16InjectedMasterState
        calls::Int
        extract_calls::Int
        witness::Any
        extracted::Any
        positive_trigger::Float64
        threads::Int
        column_counts::Vector{Int}
    end
    const FIX16_INJECTED_MASTER_STATE = Ref{Union{Nothing,FIX16InjectedMasterState}}(nothing)

    function symbolic_master(columns::Vector{IntegerPattern},
            ::FIX16InjectedUncertaintyFactory, ::FIX16InjectedSymbolicBuilder,
            optimizer; ray=false, seconds=600.0)
        ray || error(\"FIX16_INJECTED_MASTER_EXPECTED_RAY_MODE\")
        optimizer === HiGHS.Optimizer || error(\"FIX16_INJECTED_MASTER_EXPECTED_HIGHS\")
        state = FIX16_INJECTED_MASTER_STATE[]
        state === nothing && error(\"FIX16_INJECTED_MASTER_STATE_NOT_SET\")
        state.calls += 1
        push!(state.column_counts, length(columns))
        state.calls == 1 || error(\"FIX16_INJECTED_MASTER_CALLED_MORE_THAN_ONCE\")
        m = Model(HiGHS.Optimizer)
        set_silent(m)
        set_time_limit_sec(m, Float64(seconds))
        set_optimizer_attribute(m, \"threads\", state.threads)
        set_optimizer_attribute(m, \"presolve\", \"on\")
        @variable(m, eta >= 0.0)
        @constraint(m, eta <= state.positive_trigger)
        @objective(m, Max, eta)
        function extract_injected_witness()
            state.extract_calls += 1
            state.extracted = deepcopy(state.witness)
            return deepcopy(state.extracted)
        end
        return m, extract_injected_witness
    end
end

function g742_fix16_native_branch_audit(o, cfg, grids, st, z0, state_sha, scope, domain)
    isfile(joinpath(o.output, \"FIX16_NATIVE_EVENTS.tsv\")) && rm(joinpath(o.output, \"FIX16_NATIVE_EVENTS.tsv\"))
    g742_fix16_event(o, \"START\"; detail=\"native_solve_native_ccg_control_flow;diagnostic_injected_master\")
    o.branch == \"paper_zero\" || error(\"FIX16_BRANCH_PAPER_ZERO_ONLY\")
    o.witness_pattern == \"all-plus\" || error(\"FIX16_PATTERN_ALL_PLUS_ONLY\")
    o.iters == 1 || error(\"FIX16_KEEP_MAX_ITERATIONS_ONE\")
    g742_fix15_1_csv_selftest(joinpath(G742_ROOT, \"FIX14_EVIDENCE\"))
    g742_fix16_event(o, \"CSV_AND_FIX14_EVIDENCE_VERIFIED\"; detail=\"parser=FIX15.1;archived_Farkas_ray=FIX14\")
    proof = g742_fix15_evidence(o, state_sha, scope)
    prior = g742_fix16_verify_fix15_1(o, state_sha, scope, proof)
    g742_fix16_event(o, \"FIX15_1_REPLAY_EVIDENCE_VERIFIED\";
        detail=\"scenario_sha256=\$(prior.scenario_hash) alternative_hamming=\$(prior.alternative_hamming_distance)\")

    # Use the exact first scenario selected by production solve_native_stage.
    seed = first(domain.factory())
    validate_scenario(3, seed)
    witness, witness_audit = g742_fix13_realization(\"all-plus\")
    validate_scenario(3, seed); validate_scenario(3, witness)
    witness_bytes = g742_fix15_numeric_bytes(witness)
    witness_hash = bytes2hex(sha256(witness_bytes))
    witness_hash == prior.scenario_hash || error(\"FIX16_WITNESS_DIFFERS_FROM_ARCHIVED_FIX15_1_SCENARIO\")
    seed_hash = bytes2hex(sha256(g742_fix15_numeric_bytes(seed)))
    seed_hash != witness_hash || error(\"FIX16_PRODUCTION_SEED_EQUALS_INJECTED_WITNESS\")
    state_before = encode_state(st, grids)
    z0_before = copy(z0)
    empty!(REVCSCertifiedCore.SOLVER_TRACE)

    builder_calls = NamedTuple[]
    builder = function (u)
        validate_scenario(3, u)
        h = bytes2hex(sha256(g742_fix15_numeric_bytes(u)))
        push!(builder_calls, (;scenario_sha256=h, scenario_name=string(get(u, \"name\", \"\"))))
        first(build_certified_stage(3, st, u, grids;
            direction=:lower, lower_cuts=REVCSCertifiedCore.BinaryCut[],
            seconds=o.seconds, capacity_mode=cfg.capacity_mode,
            initial_station_state=z0))
    end

    injection = REVCSCertifiedCore.FIX16InjectedMasterState(
        0, 0, deepcopy(witness), nothing, 1.0, o.threads, Int[])
    REVCSCertifiedCore.FIX16_INJECTED_MASTER_STATE[] = injection
    native_result = nothing
    try
        g742_fix16_event(o, \"NATIVE_CCG_START\"; detail=\"max_iters=\$(o.iters);seed=production_first_domain_scenario;witness=all-plus\")
        native_result = REVCSCertifiedCore.solve_native_ccg(
            builder,
            REVCSCertifiedCore.FIX16InjectedUncertaintyFactory(),
            REVCSCertifiedCore.FIX16InjectedSymbolicBuilder(),
            seed;
            optimizer=HiGHS.Optimizer, scope, max_iters=o.iters,
            seconds=o.seconds, rtol=o.gap, farkas_optimizer=HiGHS.Optimizer,
            bound_role=:exact)
    finally
        REVCSCertifiedCore.FIX16_INJECTED_MASTER_STATE[] = nothing
    end

    branch_reached = injection.calls == 1 && injection.extract_calls == 1 && injection.extracted !== nothing &&
        length(native_result.history) == 1 && native_result.history[1].phase == :feasibility &&
        native_result.reason == :iteration_limit
    write_rows(joinpath(o.output, \"FIX16_NATIVE_BRANCH.csv\"), [(;
        branch=o.branch, stage=3, native_solve_native_ccg_executed=true,
        native_witness_branch_executed=branch_reached,
        native_history_phase=length(native_result.history) == 1 ? string(native_result.history[1].phase) : \"NOT_REACHED\",
        native_result_reason=string(native_result.reason), max_iterations=o.iters,
        injected_symbolic_master_calls=injection.calls,
        injected_extract_closure_calls=injection.extract_calls,
        injected_positive_gate_trigger=injection.positive_trigger,
        injected_master_column_counts=join(injection.column_counts, \";\"),
        native_columns_after_first_inner=length(native_result.columns),
        production_seed_scenario_sha256=seed_hash,
        injected_master_used=(injection.calls > 0), production_symbolic_master_executed=false,
        production_full_farkas_master_solved=false, production_extract_f_executed=false,
        root_cut_added=false, global_cut_added=false, other_patterns_excluded=false,
        full_phi3_certified=false)])

    if !branch_reached
        write_rows(joinpath(o.output, \"FIX16_SCENARIO_HANDOFF.csv\"), [(;
            branch=o.branch, scenario_pattern=\"all-plus\", scenario_sha256=witness_hash,
            predecessor_sha256=state_sha, native_branch_reached=false,
            extracted_candidate_verified=false, next_inner_builder_replayed=false,
            full_phi3_certified=false)])
        write_rows(joinpath(o.output, \"FIX16_NEXT_INNER_BUILD.csv\"), NamedTuple[])
        write_rows(joinpath(o.output, \"FIX16_NEXT_INNER_REPLAY.csv\"), NamedTuple[])
        write_rows(joinpath(o.output, \"FIX16_INJECTED_MASTER_TRACE.csv\"), [(;
            calls=injection.calls, extract_calls=injection.extract_calls,
            positive_trigger=injection.positive_trigger, production_master=false)])
        write_rows(joinpath(o.output, \"FIX16_INNER_SOLVER_TRACE.csv\"), REVCSCertifiedCore.SOLVER_TRACE)
        g742_fix16_event(o, \"NATIVE_WITNESS_BRANCH_NOT_REACHED\";
            detail=\"seed_inner_did_not_reach_a_feasible_incumbent_or_witness_gate\")
        g742_fix16_event(o, \"COMPLETE\"; detail=\"native_branch_not_reached;unresolved;Phi3_not_certified\")
        return (;status=\"NATIVE_WITNESS_BRANCH_NOT_REACHED_UNRESOLVED\", branch_reached=false,
            injected_master_used=(injection.calls > 0), next_inner_feasible=false,
            full_phi3_oracle_certified=false)
    end

    extracted = deepcopy(injection.extracted)
    extracted_hash = bytes2hex(sha256(g742_fix15_numeric_bytes(extracted)))
    extracted_hash == witness_hash || error(\"FIX16_EXTRACTED_WITNESS_HASH_MISMATCH\")
    length(builder_calls) == 1 || error(\"FIX16_UNEXPECTED_BUILDER_CALL_COUNT_BEFORE_REPLAY\")
    builder_calls[1].scenario_sha256 == seed_hash || error(\"FIX16_NATIVE_SEED_BUILDER_HASH_MISMATCH\")
    encode_state(st, grids) == state_before && z0 == z0_before ||
        error(\"FIX16_NATIVE_CCG_MUTATED_PREDECESSOR\")

    # The actual native function's one-iteration witness branch has now executed.
    # With MaxIterations fixed at one, the next-Inner build is replayed separately
    # using the exact extracted candidate; it is NOT misreported as iteration 2.
    g742_fix16_event(o, \"NATIVE_WITNESS_BRANCH_EXECUTED\";
        detail=\"phase=feasibility;candidate_sha256=\$extracted_hash;native_loop_budget=1\")
    next_inner = REVCSCertifiedCore.ensure_solver_column!(builder(extracted))
    length(builder_calls) == 2 || error(\"FIX16_NEXT_INNER_BUILDER_CALL_MISSING\")
    builder_calls[2].scenario_sha256 == extracted_hash || error(\"FIX16_NEXT_INNER_BUILDER_RECEIVED_WRONG_CANDIDATE\")
    vars = num_variables(next_inner)
    cons = num_constraints(next_inner; count_variable_in_set_constraints=true)
    intvars = filter(v -> is_binary(v) || is_integer(v), all_variables(next_inner))
    layout = [index(v).value for v in intvars]
    layout == proof.integer_indices || error(\"FIX16_NEXT_INNER_INTEGER_LAYOUT_DRIFT\")
    vars == 75481 && cons == 153238 && length(layout) == 4180 ||
        error(\"FIX16_NEXT_INNER_MODEL_SIZE_DRIFT\")
    bytes2hex(sha256(g742_fix15_numeric_bytes(extracted))) == extracted_hash ||
        error(\"FIX16_BUILDER_MUTATED_WITNESS\")
    encode_state(st, grids) == state_before && z0 == z0_before ||
        error(\"FIX16_NEXT_INNER_BUILDER_MUTATED_PREDECESSOR\")

    write_rows(joinpath(o.output, \"FIX16_SCENARIO_HANDOFF.csv\"), [(;
        branch=o.branch, scenario_pattern=\"all-plus\", scenario_sha256=extracted_hash,
        predecessor_sha256=state_sha, archived_manifest_sha256=prior.archived_manifest_sha256,
        archived_original_pattern_sha256=bytes2hex(sha256(read(joinpath(G742_ROOT,\"FIX14_EVIDENCE\",\"FIX13_INNER_INTEGER_PATTERN.tsv\")))),
        archived_fix15_1_alternative_pattern_sha256=prior.alternative_hash,
        scenario_matches_archived_fix15_1=true, native_branch_reached=true,
        injected_extract_closure_called=true, next_inner_builder_received_extracted_candidate=true,
        scenario_unchanged=true, predecessor_unchanged=true,
        production_extract_f_executed=false, production_farkas_master_solved=false,
        root_cut_added=false, other_patterns_excluded=false, full_phi3_certified=false)])
    write_rows(joinpath(o.output, \"FIX16_NEXT_INNER_BUILD.csv\"), [(;
        branch=o.branch, scenario_sha256=extracted_hash, predecessor_sha256=state_sha,
        model_variables=vars, model_constraints=cons, integer_variable_count=length(layout),
        integer_layout_matches_fix14=true, scenario_unchanged_during_build=true,
        predecessor_unchanged_during_build=true, lower_cuts=0, root_cuts_added=0,
        source=\"frozen_build_certified_stage\", seconds_per_solve=o.seconds,
        threads=o.threads, max_iterations=o.iters, outer_relative_gap=o.gap,
        native_second_iteration_executed=false, full_phi3_certified=false)])

    set_time_limit_sec(next_inner, Float64(o.seconds))
    g742_fix16_event(o, \"NEXT_INNER_REPLAY_START\"; detail=\"separate_replay_after_native_branch;seconds=\$(o.seconds)\")
    REVCSCertifiedCore.solve_tracked!(next_inner; context=\"g742_fix16_next_inner_after_native_witness_branch\")
    row = REVCSCertifiedCore.min_bounds(next_inner)
    termination = string(termination_status(next_inner))
    primal = string(primal_status(next_inner))
    differs = false; hamming = -1; zero_to_one = -1; one_to_zero = -1
    p = nothing
    if row.feasible
        p = REVCSCertifiedCore.integer_pattern(next_inner)
        p.indices == proof.integer_indices || error(\"FIX16_SOLVED_PATTERN_LAYOUT_DRIFT\")
        differs = p.values != proof.integer_values
        hamming = count(i -> p.values[i] != proof.integer_values[i], eachindex(p.values))
        zero_to_one = count(i -> proof.integer_values[i] == 0 && p.values[i] == 1, eachindex(p.values))
        one_to_zero = count(i -> proof.integer_values[i] == 1 && p.values[i] == 0, eachindex(p.values))
        differs || error(\"FIX16_ARCHIVED_INFEASIBLE_PATTERN_REAPPEARED_FEASIBLE\")
        open(joinpath(o.output, \"FIX16_NEXT_INNER_INTEGER_PATTERN.tsv\"), \"w\") do io
            println(io, \"variable_index\\tvalue\")
            for (ix, val) in zip(p.indices, p.values)
                println(io, ix, '\\t', val)
            end
        end
    end
    write_rows(joinpath(o.output, \"FIX16_INNER_SOLVER_TRACE.csv\"), REVCSCertifiedCore.SOLVER_TRACE)
    write_rows(joinpath(o.output, \"FIX16_NEXT_INNER_REPLAY.csv\"), [(;
        branch=o.branch, uncertainty_pattern=\"all-plus\", scenario_sha256=extracted_hash,
        predecessor_sha256=state_sha, solve_termination=termination, primal_status=primal,
        feasible_incumbent=row.feasible, inner_lower_bound=row.lower, inner_upper_bound=row.upper,
        incumbent_differs_from_fix14_infeasible_pattern=row.feasible ? differs : \"NOT_AVAILABLE\",
        hamming_distance_from_fix14=row.feasible ? hamming : \"NOT_AVAILABLE\",
        zero_to_one=row.feasible ? zero_to_one : \"NOT_AVAILABLE\",
        one_to_zero=row.feasible ? one_to_zero : \"NOT_AVAILABLE\",
        matches_fix15_1_alternative_pattern=(p !== nothing && p.values == prior.alternative_values),
        production_native_second_iteration_executed=false,
        production_full_farkas_master_solved=false, root_cut_added=false,
        other_patterns_excluded=false, full_phi3_certified=false)])
    write_rows(joinpath(o.output, \"FIX16_INJECTED_MASTER_TRACE.csv\"), [(;
        calls=injection.calls, extract_calls=injection.extract_calls,
        column_counts=join(injection.column_counts, \";\"), positive_trigger=injection.positive_trigger,
        synthetic_master_status=\"OPTIMAL\", synthetic_master_objective=injection.positive_trigger,
        synthetic_master_constraints=2, production_master=false)])

    g742_fix16_event(o, \"NEXT_INNER_REPLAY_DONE\";
        detail=\"termination=\$termination feasible=\$(row.feasible) alternative_pattern=\$differs hamming=\$hamming\")
    status = row.feasible ? \"NATIVE_WITNESS_BRANCH_AND_NEXT_INNER_REPLAY_COMPLETED_NOT_CERTIFIED\" :
        \"NATIVE_WITNESS_BRANCH_REACHED_NEXT_INNER_UNRESOLVED\"
    g742_fix16_event(o, \"COMPLETE\"; detail=\"native_branch_exercised=true;injected_master=true;production_farkas_master=false;Phi3_not_certified\")
    return (;status, branch_reached=true, injected_master_used=true,
        next_inner_feasible=row.feasible, alternative_pattern_differs=differs,
        hamming_distance=hamming, full_phi3_oracle_certified=false)
end
""")
    resource20("REVCS19_G7_4_2_FIX17_PRODUCTION_FARKAS.jl","65243635a38e0d264ce8126596e609b1f11502fc95570cc2001cb68f313c2abb","""# FIX17: run the frozen native C&CG path with the real production symbolic Farkas master.
# Only diagnostic wrappers and evidence writers are added; the physical model and
# REVCSCertifiedCore implementation remain byte-for-byte frozen.

const G742_FIX17_FIX16_EVIDENCE_FILES = (
    \"FIX16_NATIVE_BRANCH.csv\", \"FIX16_SCENARIO_HANDOFF.csv\",
    \"FIX16_NEXT_INNER_BUILD.csv\", \"FIX16_NEXT_INNER_REPLAY.csv\",
    \"FIX16_INNER_SOLVER_TRACE.csv\", \"FIX16_INJECTED_MASTER_TRACE.csv\",
    \"FIX16_NATIVE_EVENTS.tsv\", \"GATE_STATUS.txt\", \"RUNNER_SUMMARY.csv\",
    \"FIX16_STDOUT.log\", \"FIX16_PARSE_STDOUT.log\", \"FIX16_STATIC_STDOUT.log\")

function g742_fix17_event(o, phase; detail=\"\")
    println(\"G742_FIX17 phase=\$(phase) detail=\$(detail)\"); flush(stdout)
    open(joinpath(o.output, \"FIX17_NATIVE_EVENTS.tsv\"), \"a\") do io
        println(io, phase, '\\t', detail); flush(io)
    end
    return nothing
end

function g742_fix17_verify_fix16_evidence(o, state_sha)
    o.branch == \"paper_zero\" || error(\"FIX17_PAPER_ZERO_ONLY\")
    o.iters == 1 || error(\"FIX17_MAX_ITERATIONS_MUST_REMAIN_ONE\")
    dir = joinpath(G742_ROOT, \"FIX16_EVIDENCE\")
    manifest = joinpath(dir, \"FIX16_EVIDENCE_MANIFEST.tsv\")
    isfile(manifest) || error(\"FIX17_FIX16_EVIDENCE_MANIFEST_MISSING\")
    lines = readlines(manifest)
    length(lines) == length(G742_FIX17_FIX16_EVIDENCE_FILES) + 1 && first(lines) == \"sha256\\tfile\" ||
        error(\"FIX17_FIX16_EVIDENCE_MANIFEST_MALFORMED\")
    found = Set{String}()
    for line in lines[2:end]
        f = split(line, '\\t')
        length(f) == 2 || error(\"FIX17_FIX16_EVIDENCE_MANIFEST_ROW_INVALID\")
        expected, rel = f
        rel in G742_FIX17_FIX16_EVIDENCE_FILES && !(rel in found) ||
            error(\"FIX17_FIX16_EVIDENCE_MANIFEST_DUPLICATE_OR_UNKNOWN\")
        path = joinpath(dir, rel)
        isfile(path) && bytes2hex(sha256(read(path))) == expected ||
            error(\"FIX17_FIX16_EVIDENCE_HASH_MISMATCH: \$rel\")
        push!(found, rel)
    end
    length(found) == length(G742_FIX17_FIX16_EVIDENCE_FILES) || error(\"FIX17_FIX16_EVIDENCE_INCOMPLETE\")

    branch = g742_csvone(joinpath(dir, \"FIX16_NATIVE_BRANCH.csv\"))
    handoff = g742_csvone(joinpath(dir, \"FIX16_SCENARIO_HANDOFF.csv\"))
    replay = g742_csvone(joinpath(dir, \"FIX16_NEXT_INNER_REPLAY.csv\"))
    injected = g742_csvone(joinpath(dir, \"FIX16_INJECTED_MASTER_TRACE.csv\"))
    runner = g742_csvone(joinpath(dir, \"RUNNER_SUMMARY.csv\"))
    status = Dict{String,String}()
    for line in readlines(joinpath(dir, \"GATE_STATUS.txt\"))
        occursin('=', line) || continue
        k,v = split(line, '='; limit=2); status[k] = v
    end
    (runner[\"RunnerFix\"] == \"FIX16\" && runner[\"Mode\"] == \"native-witness-branch-audit\" &&
     runner[\"ModeEvidenceValid\"] == \"True\" && runner[\"JuliaProcessExit\"] == \"0\" &&
     status[\"GATE_7_4_2_STATUS\"] == \"NATIVE_WITNESS_BRANCH_AND_NEXT_INNER_REPLAY_COMPLETED_NOT_CERTIFIED\" &&
     status[\"FIX16_NATIVE_WITNESS_BRANCH_EXECUTED\"] == \"YES\" &&
     status[\"FIX16_INJECTED_SYMBOLIC_MASTER_USED\"] == \"YES\" &&
     status[\"FIX16_PRODUCTION_FULL_FARKAS_MASTER_SOLVED\"] == \"NO\" &&
     status[\"FULL_PHI3_ORACLE_CERTIFIED\"] == \"NO\") || error(\"FIX17_FIX16_RUN_NOT_VALID\")
    (branch[\"native_witness_branch_executed\"] == \"true\" &&
     branch[\"production_symbolic_master_executed\"] == \"false\" &&
     branch[\"production_full_farkas_master_solved\"] == \"false\" &&
     branch[\"production_extract_f_executed\"] == \"false\" &&
     branch[\"root_cut_added\"] == \"false\" && branch[\"max_iterations\"] == \"1\") ||
        error(\"FIX17_FIX16_BRANCH_EVIDENCE_INVALID\")
    (handoff[\"predecessor_sha256\"] == state_sha && handoff[\"production_farkas_master_solved\"] == \"false\" &&
     handoff[\"production_extract_f_executed\"] == \"false\" && handoff[\"root_cut_added\"] == \"false\") ||
        error(\"FIX17_FIX16_HANDOFF_EVIDENCE_INVALID\")
    (replay[\"predecessor_sha256\"] == state_sha && replay[\"feasible_incumbent\"] == \"true\" &&
     replay[\"production_full_farkas_master_solved\"] == \"false\" && replay[\"production_native_second_iteration_executed\"] == \"false\") ||
        error(\"FIX17_FIX16_REPLAY_EVIDENCE_INVALID\")
    (injected[\"production_master\"] == \"false\" && injected[\"synthetic_master_status\"] == \"OPTIMAL\" &&
     injected[\"extract_calls\"] == \"1\") || error(\"FIX17_FIX16_INJECTED_MASTER_EVIDENCE_INVALID\")
    return (; manifest_sha256=bytes2hex(sha256(read(manifest))),
        scenario_sha256=handoff[\"scenario_sha256\"], predecessor_sha256=state_sha,
        alternative_pattern_sha256=handoff[\"archived_fix15_1_alternative_pattern_sha256\"])
end

function g742_fix17_write_scenario_snapshot(path, scenario)
    open(path, \"w\") do io
        println(io, \"component\\tindex\\tvalue\")
        for key in sort(collect(keys(scenario)))
            key == \"name\" && continue
            v = scenario[key]
            if v isa Number
                println(io, key, \"\\tscalar\\t\", repr(Float64(v)))
            elseif v isa AbstractArray
                for I in CartesianIndices(v)
                    idx = join(Tuple(I), \",\")
                    println(io, key, '\\t', idx, '\\t', repr(Float64(v[I])))
                end
            else
                error(\"FIX17_UNSUPPORTED_SCENARIO_COMPONENT: \$key\")
            end
        end
    end
    return bytes2hex(sha256(read(path)))
end

function g742_fix17_write_bits(path, bits)
    open(path, \"w\") do io
        println(io, \"coordinate\\tsign\\tvalue\")
        for i in 1:2:length(bits)
            println(io, div(i+1,2), \"\\tplus\\t\", Int(round(bits[i])))
            println(io, div(i+1,2), \"\\tminus\\t\", Int(round(bits[i+1])))
        end
    end
    return nothing
end

function g742_fix17_write_pattern(path, pattern)
    open(path, \"w\") do io
        println(io, \"variable_index\\tvalue\")
        for (i,v) in zip(pattern.indices, pattern.values)
            println(io, i, '\\t', v)
        end
    end
    return nothing
end

function g742_fix17_native_production_farkas_audit(o, cfg, grids, st, z0, state_sha, scope, domain)
    isfile(joinpath(o.output, \"FIX17_NATIVE_EVENTS.tsv\")) && rm(joinpath(o.output, \"FIX17_NATIVE_EVENTS.tsv\"))
    g742_fix17_event(o, \"START\"; detail=\"frozen_native_ccg;production_symbolic_master;no_injected_master\")
    REVCSCertifiedCore.FIX19_ACTIVE[] = true
    REVCSCertifiedCore.FIX19_OUTPUT_PATH[] = o.output
    REVCSCertifiedCore.FIX19_MASTER_REF[] = nothing
    REVCSCertifiedCore.FIX19_START_TRACE[] = nothing
    REVCSCertifiedCore.FIX19_NATIVE_START_AT[] = time()
    o.branch == \"paper_zero\" || error(\"FIX17_BRANCH_PAPER_ZERO_ONLY\")
    o.witness_pattern == \"all-plus\" || error(\"FIX17_KEEP_WITNESS_PATTERN_ALL_PLUS\")
    o.iters == 1 || error(\"FIX17_KEEP_MAX_ITERATIONS_ONE\")
    fix16 = g742_fix17_verify_fix16_evidence(o, state_sha)
    g742_fix17_event(o, \"FIX16_EVIDENCE_VERIFIED\"; detail=\"manifest=\$(fix16.manifest_sha256)\")

    seed = first(domain.factory())
    validate_scenario(3, seed)
    seed_hash = bytes2hex(sha256(g742_fix15_numeric_bytes(seed)))
    state_before = copy(encode_state(st, grids))
    z0_before = copy(z0)

    builder_calls = NamedTuple[]
    builder = function (u)
        validate_scenario(3, u)
        h = bytes2hex(sha256(g742_fix15_numeric_bytes(u)))
        push!(builder_calls, (;scenario_sha256=h))
        return first(build_certified_stage(3, st, u, grids;
            direction=:lower, lower_cuts=REVCSCertifiedCore.BinaryCut[],
            seconds=o.seconds, capacity_mode=cfg.capacity_mode,
            initial_station_state=z0))
    end

    factory_calls = Ref(0)
    symbolic_builder_calls = Ref(0)
    extract_records = NamedTuple[]
    extracted_scenarios = Dict{Int,Any}()
    extracted_bits = Dict{Int,Vector{Float64}}()
    uncertainty_bit_counts = Int[]
    uncertainty_factory = function (m)
        factory_calls[] += 1
        call_id = factory_calls[]
        z, unc, extract = symbolic_uncertainty(m, 3)
        push!(uncertainty_bit_counts, length(z))
        function audited_extract()
            raw = Float64.(value.(z))
            integrality_residual = maximum(abs.(raw .- round.(raw)); init=0.0)
            pair_violation = length(raw) % 2 == 0 ? maximum(raw[1:2:end] .+ raw[2:2:end] .- 1.0; init=0.0) : Inf
            all(x -> -1e-8 <= x <= 1.0 + 1e-8, raw) || error(\"FIX17_EXTRACTED_UNCERTAINTY_OUT_OF_BOUNDS\")
            integrality_residual <= 1e-5 || error(\"FIX17_EXTRACTED_UNCERTAINTY_NONBINARY\")
            pair_violation <= 1e-8 || error(\"FIX17_EXTRACTED_UNCERTAINTY_PLUS_MINUS_OVERLAP\")
            scenario = extract() # Calls the frozen production extract closure.
            validate_scenario(3, scenario)
            scenario_hash = bytes2hex(sha256(g742_fix15_numeric_bytes(scenario)))
            role = call_id == 1 ? \"FARKAS_MASTER\" : call_id == 3 ? \"OPTIMALITY_MASTER\" : \"UNEXPECTED_AUXILIARY\"
            role == \"UNEXPECTED_AUXILIARY\" && error(\"FIX17_AUXILIARY_EXTRACT_CLOSURE_CALLED\")
            haskey(extracted_scenarios, call_id) && error(\"FIX17_EXTRACT_CLOSURE_CALLED_MORE_THAN_ONCE\")
            extracted_scenarios[call_id] = deepcopy(scenario)
            extracted_bits[call_id] = raw
            push!(extract_records, (;factory_call=call_id, role, uncertainty_binary_count=length(raw),
                integrality_residual, plus_minus_violation=pair_violation,
                scenario_sha256=scenario_hash, scenario_valid=true))
            return scenario
        end
        return z, unc, audited_extract
    end

    symbolic_builder = function (m, u)
        symbolic_builder_calls[] += 1
        return build_certified_stage(3, st, u, grids;
            direction=:lower, lower_cuts=REVCSCertifiedCore.BinaryCut[],
            seconds=o.seconds, capacity_mode=cfg.capacity_mode,
            initial_station_state=z0, shared_model=m)
    end

    # Resolve the method that the actual native call will dispatch to. The FIX16
    # marker overload cannot match these production closure types.
    farkas_optimizer = REVCSCertifiedCore.FIX18SignAwareFarkasOptimizer(
        optimizer_with_attributes(HiGHS.Optimizer,
            \"threads\" => o.threads, \"presolve\" => \"on\"), o.threads)
    production_method = which(REVCSCertifiedCore.symbolic_master,
        Tuple{Vector{REVCSCertifiedCore.IntegerPattern}, typeof(uncertainty_factory),
              typeof(symbolic_builder), typeof(farkas_optimizer)})
    method_file = basename(string(production_method.file))
    method_line = Int(production_method.line)
    method_file == \"REVCS19_G7_4_2_FIX18_SIGN_AWARE_PRODUCTION.jl\" && method_line > 0 ||
        error(\"FIX17_PRODUCTION_SYMBOLIC_MASTER_DISPATCH_MISMATCH: \$(method_file):\$(method_line)\")
    g742_fix17_event(o, \"PRODUCTION_MASTER_DISPATCH_VERIFIED\"; detail=\"\$(method_file):\$(method_line)\")

    empty!(REVCSCertifiedCore.SOLVER_TRACE)
    g742_fix17_event(o, \"NATIVE_CCG_START\"; detail=\"max_iters=\$(o.iters);seed=\$(seed_hash);farkas_optimizer=HiGHS;threads=\$(o.threads);presolve=on\")
    native_measurement = @timed REVCSCertifiedCore.solve_native_ccg(
        builder, uncertainty_factory, symbolic_builder, seed;
        optimizer=g7_scip_optimizer(), scope, max_iters=o.iters,
        seconds=o.seconds, rtol=o.gap, farkas_optimizer,
        feasibility_tol=1e-8, bound_role=:exact)
    native_result = native_measurement.value
    trace = copy(REVCSCertifiedCore.SOLVER_TRACE)
    write_rows(joinpath(o.output, \"FIX17_MASTER_TRACE.csv\"), trace)
    if isempty(extract_records)
        open(joinpath(o.output, \"FIX17_EXTRACT_TRACE.csv\"), \"w\") do io
            println(io, \"factory_call,role,uncertainty_binary_count,integrality_residual,plus_minus_violation,scenario_sha256,scenario_valid\")
        end
    else
        write_rows(joinpath(o.output, \"FIX17_EXTRACT_TRACE.csv\"), extract_records)
    end
    write_rows(joinpath(o.output, \"FIX17_SOLVER_CONFIG.csv\"), [
        (;parameter=\"threads\", value=o.threads, scope=\"production_farkas_master\"),
        (;parameter=\"presolve\", value=\"on\", scope=\"production_farkas_master\"),
        (;parameter=\"seconds_per_solve\", value=o.seconds, scope=\"native_inner_and_farkas_master\"),
        (;parameter=\"max_iterations\", value=o.iters, scope=\"native_ccg_outer_loop\"),
        (;parameter=\"overall_seconds\", value=600, scope=\"runner_watchdog\"),
        (;parameter=\"relative_gap\", value=o.gap, scope=\"native_ccg_outer_gap\"),
        (;parameter=\"farkas_mip_relative_gap\", value=\"solver_default_unchanged\", scope=\"not_overridden_by_FIX17\")])

    initial_rows = filter(x -> x.context == \"ccg_inner_stage_scenario\", trace)
    farkas_rows = filter(x -> x.context == \"ccg_farkas_linearized_master\", trace)
    optimality_rows = filter(x -> x.context == \"ccg_optimality_indicator_master\", trace)
    length(initial_rows) <= 1 || error(\"FIX17_MULTIPLE_INITIAL_INNER_SOLVES_UNEXPECTED\")
    length(farkas_rows) <= 1 || error(\"FIX17_MULTIPLE_FARKAS_MASTER_SOLVES_UNEXPECTED\")
    length(optimality_rows) <= 1 || error(\"FIX17_MULTIPLE_OPTIMALITY_MASTER_SOLVES_UNEXPECTED\")

    phase = isempty(native_result.history) ? \"NOT_REACHED\" : string(first(native_result.history).phase)
    gate = phase == \"feasibility\" ? \"witness\" :
           phase == \"feasibility_unresolved\" ? \"unresolved\" :
           phase == \"optimality\" ? \"covered\" : \"NOT_REACHED\"
    initial = isempty(initial_rows) ? nothing : only(initial_rows)
    fm = isempty(farkas_rows) ? nothing : only(farkas_rows)
    initial_feasible = initial !== nothing && initial.primal == \"FEASIBLE_POINT\"
    columns = native_result.columns
    length(columns) <= 1 || error(\"FIX17_EXPECTED_ONE_COLUMN_AT_MAX_ITERATIONS_ONE\")
    column = isempty(columns) ? nothing : first(columns)
    if column !== nothing
        length(column.values) == 4180 || error(\"FIX17_NATIVE_COLUMN_INTEGER_LAYOUT_MISMATCH\")
        g742_fix17_write_pattern(joinpath(o.output, \"FIX17_COLUMN_PATTERN.tsv\"), column)
    end

    production_master_executed = fm !== nothing && method_file == \"REVCS19_G7_4_2_FIX18_SIGN_AWARE_PRODUCTION.jl\" &&
        method_line > 0 && factory_calls[] >= 2 && symbolic_builder_calls[] >= 1
    # A solver attempt is not a certified Farkas conclusion.  The previous
    # reporting code conflated these concepts and referenced an undefined name.
    production_farkas_attempted = fm !== nothing
    production_farkas_solved = gate in (\"witness\", \"covered\")
    production_farkas_master_solved = production_farkas_solved
    farkas_extract_records = filter(x -> x.factory_call == 1, extract_records)
    length(farkas_extract_records) <= 1 || error(\"FIX17_DUPLICATE_PRODUCTION_FARKAS_EXTRACT\")
    production_extract_f_executed = !isempty(farkas_extract_records)
    production_extract_f_executed == (gate == \"witness\") ||
        error(\"FIX17_FARKAS_GATE_AND_EXTRACT_CALL_DISAGREE\")

    scenario_hash = \"\"
    scenario_valid = false
    replay_attempted = false
    next_termination = \"NOT_RUN\"
    next_primal = \"NOT_RUN\"
    next_feasible = false
    next_lower = NaN
    next_incumbent = Inf
    next_hamming = -1
    next_zero_to_one = -1
    next_one_to_zero = -1
    fix14_compare_applicable = false
    fix14_pattern_matches = \"NOT_APPLICABLE\"

    if production_extract_f_executed
        scenario = extracted_scenarios[1]
        validate_scenario(3, scenario)
        scenario_valid = true
        scenario_hash = bytes2hex(sha256(g742_fix15_numeric_bytes(scenario)))
        scenario_hash == only(farkas_extract_records).scenario_sha256 || error(\"FIX17_EXTRACTED_SCENARIO_HASH_DRIFT\")
        g742_fix17_write_scenario_snapshot(joinpath(o.output, \"FIX17_EXTRACTED_SCENARIO.tsv\"), scenario)
        g742_fix17_write_bits(joinpath(o.output, \"FIX17_FARKAS_UNCERTAINTY_BITS.tsv\"), extracted_bits[1])
        g742_write_scenario(o.output, scenario)
        g742_fix17_event(o, \"PRODUCTION_FARKAS_WITNESS_EXTRACTED\"; detail=\"scenario_sha256=\$scenario_hash\")

        length(builder_calls) == 1 || error(\"FIX17_INITIAL_BUILDER_CALL_COUNT_MISMATCH\")
        builder_calls[1].scenario_sha256 == seed_hash || error(\"FIX17_NATIVE_INITIAL_SEED_CHANGED\")
        encode_state(st, grids) == state_before && z0 == z0_before || error(\"FIX17_NATIVE_MUTATED_PREDECESSOR\")
        before_build_hash = bytes2hex(sha256(g742_fix15_numeric_bytes(scenario)))
        next_inner = REVCSCertifiedCore.ensure_solver_column!(builder(scenario))
        replay_attempted = true
        length(builder_calls) == 2 && builder_calls[2].scenario_sha256 == scenario_hash ||
            error(\"FIX17_NEXT_INNER_DID_NOT_RECEIVE_PRODUCTION_EXTRACTED_SCENARIO\")
        bytes2hex(sha256(g742_fix15_numeric_bytes(scenario))) == before_build_hash ||
            error(\"FIX17_NEXT_INNER_BUILDER_MUTATED_SCENARIO\")
        encode_state(st, grids) == state_before && z0 == z0_before || error(\"FIX17_NEXT_INNER_MUTATED_PREDECESSOR\")
        intvars = filter(v -> is_binary(v) || is_integer(v), all_variables(next_inner))
        integer_indices = [index(v).value for v in intvars]
        integer_indices == column.indices || error(\"FIX17_NEXT_INNER_INTEGER_LAYOUT_DRIFT\")
        model_vars = num_variables(next_inner)
        model_cons = num_constraints(next_inner; count_variable_in_set_constraints=true)
        model_vars == 75481 && model_cons == 153238 && length(intvars) == 4180 ||
            error(\"FIX17_NEXT_INNER_MODEL_DIMENSION_DRIFT\")
        write_rows(joinpath(o.output, \"FIX17_NEXT_INNER_BUILD.csv\"), [(;
            branch=o.branch, scenario_sha256=scenario_hash, predecessor_sha256=state_sha,
            model_variables=model_vars, model_constraints=model_cons,
            integer_variable_count=length(intvars), integer_layout_matches_native_column=true,
            scenario_unchanged_during_build=true, predecessor_unchanged_during_build=true,
            lower_cuts=0, root_cuts_added=0, source=\"frozen_build_certified_stage\",
            native_second_iteration_executed=false, production_farkas_master_solved=true,
            seconds_per_solve=o.seconds, threads=o.threads, max_iterations=o.iters,
            outer_relative_gap=o.gap, full_phi3_certified=false)])

        set_time_limit_sec(next_inner, Float64(o.seconds))
        g742_fix17_event(o, \"NEXT_INNER_REPLAY_START\"; detail=\"separate_replay_after_native_loop_budget_one;seconds=\$(o.seconds)\")
        REVCSCertifiedCore.solve_tracked!(next_inner; context=\"g742_fix17_next_inner_after_production_witness\")
        next_row = REVCSCertifiedCore.min_bounds(next_inner)
        next_termination = string(termination_status(next_inner))
        next_primal = string(primal_status(next_inner))
        next_feasible = next_row.feasible
        next_lower = next_row.lower
        next_incumbent = next_row.upper
        if next_feasible
            next_pattern = REVCSCertifiedCore.integer_pattern(next_inner)
            next_pattern.indices == column.indices || error(\"FIX17_REPLAY_PATTERN_LAYOUT_DRIFT\")
            next_hamming = count(i -> next_pattern.values[i] != column.values[i], eachindex(column.values))
            next_zero_to_one = count(i -> column.values[i] == 0 && next_pattern.values[i] == 1, eachindex(column.values))
            next_one_to_zero = count(i -> column.values[i] == 1 && next_pattern.values[i] == 0, eachindex(column.values))
            next_hamming > 0 || error(\"FIX17_FARKAS_COLUMN_REAPPEARED_FEASIBLE_AT_ITS_WITNESS\")
            g742_fix17_write_pattern(joinpath(o.output, \"FIX17_NEXT_INNER_INTEGER_PATTERN.tsv\"), next_pattern)
            allplus, _ = g742_fix13_realization(\"all-plus\")
            allplus_hash = bytes2hex(sha256(g742_fix15_numeric_bytes(allplus)))
            if scenario_hash == allplus_hash
                fix14_compare_applicable = true
                fix14_lines = readlines(joinpath(G742_ROOT, \"FIX14_EVIDENCE\", \"FIX13_INNER_INTEGER_PATTERN.tsv\"))
                length(fix14_lines) == 4181 || error(\"FIX17_FIX14_PATTERN_SHAPE_INVALID\")
                fix14_values = Int[parse(Int, split(line, '\\t')[2]) for line in fix14_lines[2:end]]
                fix14_pattern_matches = next_pattern.values == fix14_values
                fix14_pattern_matches && error(\"FIX17_FIX14_INFEASIBLE_PATTERN_REAPPEARED_FEASIBLE\")
            end
        end
        write_rows(joinpath(o.output, \"FIX17_NEXT_INNER_REPLAY.csv\"), [(;
            branch=o.branch, scenario_sha256=scenario_hash, predecessor_sha256=state_sha,
            solve_termination=next_termination, primal_status=next_primal,
            feasible_incumbent=next_feasible, lower_bound=next_lower, incumbent=next_incumbent,
            hamming_distance_from_native_farkas_column=next_feasible ? next_hamming : \"NOT_AVAILABLE\",
            zero_to_one=next_feasible ? next_zero_to_one : \"NOT_AVAILABLE\",
            one_to_zero=next_feasible ? next_one_to_zero : \"NOT_AVAILABLE\",
            fix14_pattern_comparison_applicable=fix14_compare_applicable,
            matches_fix14_infeasible_pattern=fix14_pattern_matches,
            production_native_second_iteration_executed=false,
            production_farkas_master_solved=true, root_cut_added=false,
            other_patterns_excluded=false, full_phi3_certified=false)])
        g742_fix17_event(o, \"NEXT_INNER_REPLAY_DONE\";
            detail=\"termination=\$next_termination feasible=\$next_feasible hamming=\$next_hamming\")
    end

    # If the gate is covered, the frozen C&CG code may have entered the separate
    # optimality master. Its extraction is recorded but is not called a Farkas witness.
    optimality_extract_records = filter(x -> x.factory_call == 3, extract_records)
    if !isempty(optimality_extract_records)
        sc = extracted_scenarios[3]
        g742_fix17_write_scenario_snapshot(joinpath(o.output, \"FIX17_OPTIMALITY_SCENARIO.tsv\"), sc)
    end

    write_rows(joinpath(o.output, \"FIX17_INNER_SOLVER_TRACE.csv\"), trace)
    # Append the separate replay trace if it was run.
    if replay_attempted
        replay_rows = filter(x -> x.context == \"g742_fix17_next_inner_after_production_witness\", REVCSCertifiedCore.SOLVER_TRACE)
        if !isempty(replay_rows)
            open(joinpath(o.output, \"FIX17_INNER_SOLVER_TRACE.csv\"), \"a\") do io
                # This file is supplementary; FIX17_MASTER_TRACE.csv preserves the native trace.
                for r in replay_rows
                    println(io, join((csvcell(getproperty(r,f)) for f in propertynames(r)), \",\"))
                end
            end
        end
    end

    # FIX18: independently report construction of the full sign-aware symbolic master.
    metrics = REVCSCertifiedCore.FIX18_LAST_BUILD_METRICS[]
    if fm !== nothing
        metrics isa AbstractDict || error(\"FIX18_PRODUCTION_MASTER_METRICS_MISSING\")
        Int(metrics[\"model_variables\"]) == fm.variables || error(\"FIX18_REPORTED_VARIABLE_COUNT_MISMATCH\")
        Int(metrics[\"model_constraints\"]) == fm.constraints || error(\"FIX18_REPORTED_CONSTRAINT_COUNT_MISMATCH\")
    elseif metrics !== nothing
        error(\"FIX18_METRICS_WITHOUT_MASTER_TRACE\")
    end
    fix18_rows = [(;
        attempted=fm !== nothing, production_dispatch_file=method_file,
        sign_aware_enabled=fm !== nothing && metrics[\"normalization_sign_aware_enabled\"] == 1,
        model_variables=fm === nothing ? -1 : fm.variables,
        model_constraints=fm === nothing ? -1 : fm.constraints,
        eliminated_abs_variables=fm === nothing ? 0 : metrics[\"sign_aware_eliminated_abs_variables\"],
        retained_free_dual_abs_variables=fm === nothing ? 0 : metrics[\"absolute_value_variables\"],
        legacy_projected_variables=fm === nothing ? -1 : metrics[\"legacy_projected_variables\"],
        legacy_projected_constraints=fm === nothing ? -1 : metrics[\"legacy_projected_constraints\"],
        uncertainty_binary_indicators=fm === nothing ? 0 : metrics[\"uncertainty_binary_indicators\"],
        variable_count_delta=fm === nothing ? \"NOT_REACHED\" : metrics[\"variable_count_delta\"],
        constraint_count_delta=fm === nothing ? \"NOT_REACHED\" : metrics[\"constraint_count_delta\"],
        farkas_gate=gate, ray_certified=gate in (\"witness\", \"covered\"),
        full_phi3_certified=false)]
    write_rows(joinpath(o.output, \"FIX18_PRODUCTION_FORMULATION.csv\"), fix18_rows)

    master_vars = fm === nothing ? -1 : fm.variables
    master_cons = fm === nothing ? -1 : fm.constraints
    master_termination = fm === nothing ? \"NOT_RUN\" : fm.termination
    master_primal = fm === nothing ? \"NOT_RUN\" : fm.primal
    master_incumbent = fm === nothing ? NaN : fm.incumbent
    master_bound = fm === nothing ? NaN : fm.bound
    status = if initial === nothing
        \"NATIVE_PRODUCTION_INNER_NOT_REACHED_UNRESOLVED\"
    elseif initial.termination == \"INFEASIBLE\"
        \"NATIVE_PRODUCTION_INNER_NO_FEASIBLE_COLUMN_UNRESOLVED\"
    elseif !initial_feasible
        \"NATIVE_PRODUCTION_INNER_NO_INCUMBENT_UNRESOLVED\"
    elseif gate == \"witness\" && next_feasible
        \"NATIVE_PRODUCTION_FARKAS_WITNESS_REPLAY_COMPLETED_NOT_CERTIFIED\"
    elseif gate == \"witness\"
        \"NATIVE_PRODUCTION_FARKAS_WITNESS_REPLAY_UNRESOLVED\"
    elseif gate == \"covered\"
        \"NATIVE_PRODUCTION_FARKAS_COVERED_OPTIMALITY_PATH_NOT_CERTIFIED\"
    elseif gate == \"unresolved\"
        \"NATIVE_PRODUCTION_FARKAS_GATE_UNRESOLVED_NOT_CERTIFIED\"
    else
        \"NATIVE_PRODUCTION_FARKAS_NOT_REACHED_UNRESOLVED\"
    end

    write_rows(joinpath(o.output, \"FIX17_NATIVE_PRODUCTION.csv\"), [(;
        branch=o.branch, stage=3, scope, predecessor_sha256=state_sha,
        seed_scenario_sha256=seed_hash, initial_inner_feasible=initial_feasible,
        initial_inner_termination=initial === nothing ? \"NOT_RUN\" : initial.termination,
        initial_inner_primal=initial === nothing ? \"NOT_RUN\" : initial.primal,
        initial_inner_variables=initial === nothing ? -1 : initial.variables,
        initial_inner_constraints=initial === nothing ? -1 : initial.constraints,
        initial_column_count=length(columns), integer_variable_count=column === nothing ? 0 : length(column.values),
        production_symbolic_master_method_file=method_file, production_symbolic_master_method_line=method_line,
        production_symbolic_master_executed=production_master_executed, uncertainty_factory_calls=factory_calls[],
        symbolic_builder_calls=symbolic_builder_calls[], uncertainty_binary_count=isempty(uncertainty_bit_counts) ? 0 : first(uncertainty_bit_counts),
        domain_cardinality=string(domain.cardinality), full_domain_symbolic=true,
        production_farkas_master_attempted=production_farkas_attempted,
        production_farkas_master_solved, farkas_master_variables=master_vars,
        farkas_master_constraints=master_cons, farkas_master_termination=master_termination,
        farkas_master_primal=master_primal, farkas_master_incumbent=master_incumbent,
        farkas_master_bound=master_bound, farkas_gate=gate,
        native_history_phase=phase, native_result_reason=string(native_result.reason),
        production_extract_f_executed, extract_factory_call=production_extract_f_executed ? 1 : \"NONE\",
        extracted_scenario_valid=scenario_valid, extracted_scenario_sha256=scenario_hash,
        scenario_replay_attempted=replay_attempted, next_inner_termination=next_termination,
        next_inner_primal=next_primal, next_inner_feasible=next_feasible,
        next_inner_lower_bound=next_lower, next_inner_incumbent=next_incumbent,
        next_inner_hamming_from_farkas_column=next_hamming,
        root_cut_added=false, global_cut_added=false, other_patterns_excluded=false,
        full_phi3_certified=false)])

    g742_fix17_event(o, \"COMPLETE\"; detail=\"production_master=\$production_farkas_solved gate=\$gate extract_f=\$production_extract_f_executed replay=\$replay_attempted status=\$status;Phi3_not_certified\")
    return (;status, production_master_executed, production_farkas_solved,
        production_farkas_attempted,
        production_extract_f_executed, scenario_valid, scenario_hash,
        replay_attempted, next_feasible, farkas_gate=gate, full_phi3_oracle_certified=false)
end
""")
    resource20("REVCS19_G7_4_2_FIX18_SIGN_AWARE_PRODUCTION.jl","7c1fcf6e622bfa206c8bddfb8f8316c20f9727074f41750f36941f8479e5a76e","""# REVCS19 Gate 7.4.2 FIX18: full production Native C&CG Farkas master
# Exact sign-aware L1 normalization, reusing the FIX9 validated symbolic construction.
# The frozen physical source and root decision data are untouched.
# Unlike the FIX16 injection, this constructs the complete uncertainty-domain Farkas MIP.
@eval REVCSCertifiedCore begin
    struct FIX18SignAwareFarkasOptimizer{T}
        inner_optimizer::T
        threads::Int
    end

    const FIX18_LAST_BUILD_METRICS = Ref{Any}(nothing)

    function symbolic_master(columns::Vector{IntegerPattern},uncertainty_factory,symbolic_builder,
            optimizer::FIX18SignAwareFarkasOptimizer;ray=false,seconds=600.0)
        ray || error(\"FIX18_SIGN_AWARE_DISPATCH_FOR_FARKAS_ONLY\")
        optimizer.threads > 0 || error(\"FIX18_INVALID_THREAD_COUNT\")
        FIX18_LAST_BUILD_METRICS[] = nothing
        # This is the full symbolic dual of every integer column over all 3,764
        # uncertainty bits, NOT a fixed-scenario LP or a synthetic 1-row master.
        result=farkas_audit_symbolic_master(columns,uncertainty_factory,symbolic_builder,
            optimizer.inner_optimizer; seconds=seconds, threads=optimizer.threads,
            sign_aware=true)
        mm=result.metrics
        get(mm,\"normalization_sign_aware_enabled\",0)==1 || error(\"FIX18_SIGN_AWARE_NOT_ENABLED\")
        get(mm,\"variable_count_delta\",-1)==0 || error(\"FIX18_VARIABLE_COUNT_INCONSISTENT\")
        get(mm,\"constraint_count_delta\",-1)==0 || error(\"FIX18_CONSTRAINT_COUNT_INCONSISTENT\")
        get(mm,\"sign_aware_eliminated_abs_variables\",0)==
            get(mm,\"less_equal_sides\",0)+get(mm,\"greater_equal_sides\",0) ||
            error(\"FIX18_SIGNED_DUAL_ELIMINATION_MISMATCH\")
        get(mm,\"absolute_value_variables\",-1)==get(mm,\"equality_sides\",0) ||
            error(\"FIX18_FREE_DUAL_NORMALIZATION_MISMATCH\")
        get(mm,\"model_variables\",-1)==217591 || error(\"FIX18_PRODUCTION_VARIABLE_COUNT_DRIFT\")
        get(mm,\"model_constraints\",-1)==612826 || error(\"FIX18_PRODUCTION_CONSTRAINT_COUNT_DRIFT\")
        get(mm,\"legacy_projected_variables\",-1)==338203 || error(\"FIX18_LEGACY_VARIABLE_PROJECTION_DRIFT\")
        get(mm,\"legacy_projected_constraints\",-1)==1095274 || error(\"FIX18_LEGACY_CONSTRAINT_PROJECTION_DRIFT\")
        get(mm,\"uncertainty_binary_indicators\",-1)==3764 || error(\"FIX18_UNCERTAINTY_BITS_DRIFT\")
        FIX18_LAST_BUILD_METRICS[] = copy(mm)
        if isdefined(@__MODULE__, :FIX19_ACTIVE) && FIX19_ACTIVE[]
            fix19_same_column_preseed!(result;seconds=Float64(seconds))
            return result.model,fix19_guarded_production_extract(result)
        end
        return result.model,result.extract
    end
end
""")
    resource20("REVCS19_G7_4_2_FIX19_SAME_COLUMN_SEED.jl","409d86b670293e2cd9cdc912d2f8358ce0de16e2a894bc03a6533a64f672c02b","""# FIX19: same-current-column, full-master fixed-scenario LP candidate and verified MIP start.
# No historical FIX14 certificate, imported integer column, synthetic dual or globally valid cut.
# This module is included AFTER FIX18 construction and BEFORE the production driver.
@eval REVCSCertifiedCore begin
    const FIX19_ACTIVE = Ref(false)
    const FIX19_OUTPUT_PATH = Ref(\"\")
    const FIX19_MASTER_REF = Ref{Any}(nothing)
    const FIX19_START_TRACE = Ref{Any}(nothing)
    const FIX19_NATIVE_START_AT = Ref(0.0)

    function fix19_emit_csv(filename::String, rows)
        dir=FIX19_OUTPUT_PATH[]
        isempty(dir) && error(\"FIX19_OUTPUT_PATH_MISSING\")
        mkpath(dir)
        isempty(rows) && error(\"FIX19_EMPTY_REPORT\")
        columns=propertynames(first(rows))
        open(joinpath(dir,filename),\"w\") do io
            println(io,join(string.(columns),\",\"))
            for row in rows
                propertynames(row)==columns || error(\"FIX19_REPORT_COLUMNS_DRIFT\")
                cells=String[]
                for key in columns
                    v=string(getproperty(row,key))
                    # RFC 4180-safe values; all numeric paths and statuses are ASCII.
                    if occursin(',',v) || occursin('\"',v) || occursin('\\n',v)
                        v=\"\\\"\" * replace(v,\"\\\"\"=>\"\\\"\\\"\") * \"\\\"\"
                    end
                    push!(cells,v)
                end
                println(io,join(cells,\",\"))
            end
        end
    end

    function fix19_primal_start_supported()
        try
            return MOI.supports(HiGHS.Optimizer(), MOI.VariablePrimalStart(), MOI.VariableIndex)
        catch
            return false
        end
    end

    # Every fixed LP uses the ORIGINAL production Farkas master and the fresh
    # 4,180-bit column returned by this invocation of solve_native_ccg.
    # Restores the EXACT MIP constraint set, regardless of LP termination.
    function fix19_same_column_preseed!(audited;seconds::Float64=90.0)
        FIX19_ACTIVE[] || error(\"FIX19_NOT_ACTIVE\")
        m=audited.model
        FIX19_MASTER_REF[] = m
        base_vars=num_variables(m)
        base_rows=num_constraints(m;count_variable_in_set_constraints=true)
        base_vars==217591 && base_rows==612826 || error(\"FIX19_FARKAS_MASTER_DIMENSION_DRIFT\")
        bits=audited.z
        length(bits)==3764 || error(\"FIX19_FULL_DOMAIN_BITS_MISMATCH\")
        allvars=all_variables(m)
        integer_vars=filter(v->is_binary(v)||is_integer(v),allvars)
        all(v->is_binary(v),integer_vars) || error(\"FIX19_UNEXPECTED_GENERAL_INTEGER\")
        length(integer_vars)==3764+length(audited.and_cache) || error(\"FIX19_BINARY_LAYOUT_MISMATCH\")
        support=fix19_primal_start_supported()
        rows=NamedTuple[]
        accepted_vector=nothing
        accepted_pattern=\"NONE\"
        accepted_objective=NaN
        start_submitted=false
        readback=0
        for pattern in (\"all-plus\",\"all-minus\",\"nominal\")
            # Reserve two 90-second solves (production MIP + possible replay)
            # and 60 seconds overhead inside the unchanged 600-second watchdog.
            # Never start an extra diagnostic LP that would predictably starve
            # the actual native MIP and its witness handoff.
            if !isempty(rows) && FIX19_NATIVE_START_AT[] > 0.0 &&
               time()-FIX19_NATIVE_START_AT[] + 3seconds + 60.0 > 600.0
                break
            end
            assignments,layout=farkas_fixed_pattern_values(bits,audited.and_cache;pattern)
            all(v->haskey(assignments,v),integer_vars) || error(\"FIX19_FIXED_PATTERN_BINARY_COVERAGE_MISMATCH\")
            fixedrows=ConstraintRef[]
            undo=nothing
            elapsed=NaN
            term=\"NOT_RUN\"; ps=\"NOT_RUN\"; incumbent=NaN
            audit_checked=0; audit_violated=-1; max_viol=NaN
            full_audit=false; bin_error=NaN
            vector=nothing
            candidate=false
            try
                for v in integer_vars
                    push!(fixedrows,@constraint(m,v==assignments[v]))
                end
                length(fixedrows)==length(integer_vars) || error(\"FIX19_FIXED_ROW_COUNT_DRIFT\")
                undo=relax_integrality(m)
                all(v->!is_binary(v) && !is_integer(v),integer_vars) ||
                    error(\"FIX19_INTEGRALITY_NOT_RELAXED\")
                set_time_limit_sec(m,seconds)
                elapsed=@elapsed optimize!(m)
                term=string(termination_status(m))
                ps=string(primal_status(m))
                feasible=has_values(m) && primal_status(m)==MOI.FEASIBLE_POINT
                if feasible
                    incumbent=Float64(objective_value(m))
                    audit=farkas_audit_mip_incumbent(m;tol=1e-5)
                    audit_checked=audit.constraints_checked
                    audit_violated=audit.violated_constraints
                    max_viol=audit.maximum_constraint_violation
                    bin_error=maximum(abs(Float64(value(v))-assignments[v]) for v in integer_vars)
                    full_audit=audit.independent_incumbent_validated && audit_violated==0 &&
                        bin_error<=1e-5 && isfinite(incumbent) &&
                        abs(Float64(value(objective_function(m)))-incumbent)<=1e-5*max(1.0,abs(incumbent))
                    # Farkas tolerance 1e-8; require an ample numerical margin.
                    candidate=full_audit && incumbent>1e-3
                    if candidate
                        vector=Float64[value(v) for v in allvars]
                        all(isfinite,vector) || error(\"FIX19_NONFINITE_CANDIDATE_VECTOR\")
                        length(vector)==base_vars || error(\"FIX19_VECTOR_LENGTH_DRIFT\")
                    end
                end
            finally
                undo !== nothing && undo()
                for row in fixedrows
                    is_valid(m,row) && delete(m,row)
                end
                num_variables(m)==base_vars || error(\"FIX19_VARIABLES_NOT_RESTORED\")
                num_constraints(m;count_variable_in_set_constraints=true)==base_rows ||
                    error(\"FIX19_CONSTRAINTS_NOT_RESTORED\")
                all(is_binary,integer_vars) || error(\"FIX19_INTEGRALITY_NOT_RESTORED\")
                set_time_limit_sec(m,seconds)
            end
            push!(rows,(;pattern,lp_termination=term,lp_primal=ps,
                lp_objective=incumbent,lp_seconds=elapsed,checked_constraints=audit_checked,
                violated_constraints=audit_violated,max_constraint_violation=max_viol,
                max_binary_fix_error=bin_error,independently_validated=full_audit,
                positive_same_column_candidate=candidate,
                full_domain_bits=layout.uncertainty_binary_variables,
                fixed_discrete_variables=length(integer_vars),
                candidate_source=\"CURRENT_PRODUCTION_MASTER_FIXED_PATTERN_LP\",
                full_phi3_certified=false))
            if candidate
                accepted_vector=vector
                accepted_pattern=pattern
                accepted_objective=incumbent
                break
            end
        end
        # A valid LP ray is NOT automatically an accepted HiGHS MIP start.
        if accepted_vector !== nothing && support
            for (v,x) in zip(allvars,accepted_vector)
                set_start_value(v,x)
            end
            for (v,x) in zip(allvars,accepted_vector)
                a=start_value(v)
                a!==nothing && isfinite(a) && abs(a-x)<=1e-8 ||
                    error(\"FIX19_START_VALUE_READBACK_MISMATCH\")
                readback+=1
            end
            readback==base_vars || error(\"FIX19_INCOMPLETE_MIP_START\")
            start_submitted=true
        end
        report=(;current_column_source=\"solve_native_ccg:initial_inner_integer_pattern\",
            full_domain_uncertainty_bits=length(bits),master_variables=base_vars,
            master_constraints=base_rows,lp_patterns_tested=length(rows),
            validated_positive_lp_candidate=(accepted_vector !== nothing),
            positive_lp_pattern=accepted_pattern,positive_lp_objective=accepted_objective,
            primal_start_moi_supported=support,start_values_submitted=start_submitted ? base_vars : 0,
            start_values_readback=readback,mip_start_requested=start_submitted,
            solver_acceptance=\"UNVERIFIED\",mip_incumbent_observed=\"NOT_YET_SOLVED\",
            root_cut_added=false,oracle_certified=false)
        FIX19_START_TRACE[]=report
        fix19_emit_csv(\"FIX19_FIXED_PATTERN_LP.csv\",rows)
        fix19_emit_csv(\"FIX19_MIP_START.csv\",[report])
        return report
    end

    # Called only AFTER the unchanged production Farkas MIP reports a positive
    # incumbent and the original native C&CG enters the witness extraction branch.
    function fix19_guarded_production_extract(audited)
        return function ()
            m=audited.model
            has_values(m) && primal_status(m)==MOI.FEASIBLE_POINT ||
                error(\"FIX19_PRODUCTION_WITNESS_NO_SOLVER_INCUMBENT\")
            inc=Float64(objective_value(m))
            audit=farkas_audit_mip_incumbent(m;tol=1e-5)
            verified=audit.independent_incumbent_validated && audit.violated_constraints==0 &&
                isfinite(inc) && inc>1e-3
            fix19_emit_csv(\"FIX19_PRODUCTION_INCUMBENT_AUDIT.csv\",[(;
                solver_termination=string(termination_status(m)),
                solver_primal=string(primal_status(m)),incumbent=inc,
                constraints_checked=audit.constraints_checked,
                violated_constraints=audit.violated_constraints,
                maximum_violation=audit.maximum_constraint_violation,
                independently_validated=verified,positive_witness=verified,
                solver_start_acceptance=\"UNVERIFIED\",full_phi3_certified=false)])
            verified || error(\"FIX19_UNVALIDATED_PRODUCTION_FARKAS_WITNESS_REJECTED\")
            return audited.extract()  # exactly the original production extractor
        end
    end
end
""")
    resource20("REVCS19_GATE7_3_4_BOUNDSFIX.jl","70f976f717ab3674ea7142717f62dc6b6c125bc3da4ec04f321c968efd1eb8f5","""# ==============================================================================
# REVCS19 Gate 7 controlled C&CG integration candidate with two explicit initial-station branches
# ==============================================================================
# این فایل کاندید کنترل‌شدهٔ یکپارچه‌سازی است؛ هنوز با Gate 6.4 ادغام یا تأیید نهایی نشده است.
# تمام تغییرات Gate 7 در شاخهٔ جداگانه نگه داشته می‌شوند و فایل Gate 6.4 دست‌نخورده می‌ماند.
# شاخه existing_five مبنای مورد مطالعه در جدول ۱ مکمل است؛ paper_zero حساسیت لفظی Eq37 است.
# این فایل مستقل شامل داده‌های موجود شبکه، مدل فیزیکی، کدگذاری دودویی حالت،
# C&CG نمادین و مرجع، برش لاگرانژی و تقریب بالایی دارای گواه روی دامنهٔ صریح است.
# مبنای الگوریتمی از کاندید REVCS18 گرفته شده؛ این فایل هنوز ادغام نهایی با REVCS19 Gate 6.4 نیست.
# تغییرات این فایل فقط برای ممیزی/تفکیک وضعیت اولیه و کنترل هویت گواه‌ها اعمال شده‌اند.
# متن توضیح بالای هر خط آمده تا ادامهٔ عبارت‌های چندخطی و ماکروهای JuMP سالم بماند.
# دقت ظرفیت‌ها باید هنگام فراخوانی state_grids صریحاً تعیین شود؛ مقداری به نام مقاله ساخته نشده است.
# شبکهٔ محدود ظرفیت، معادل تمام مقادیر حقیقی مدل پیوسته یا گواه خطای گسسته‌سازی نیست.
# فقط تقسیم یکنواخت بار مستند به جدول ۸ پیوست است؛ SOC و چرخهٔ باتری فرض‌های مهندسی صریح و قابل تنظیم‌اند.
# تعارض تفسیر ظرفیت شارژ در معادلهٔ ۳۳ با گزینهٔ capacity_mode صریح باقی می‌ماند.
# UpperSample فقط از کران بالای حل مقاوم با نقش exact یا upper ساخته می‌شود.
# تقریب بالایی روی مجموعهٔ حالت‌های گواهی‌شده که عضویت در آن به مدل تحمیل می‌شود معتبر است.
# معتبر بودن اجزای کران‌سازی، ادعای همگرایی افق کامل یا بازتولید صددرصدی مقاله نیست.
# اجرای مستقیم فایل، گزارش پیکربندی می‌دهد؛ حل دوره‌ها از رابط‌های تعریف‌شده فراخوانی می‌شود.
# پیش‌نیاز اجرا: محیط جولیا دارای JuMP، MathOptInterface، HiGHS و SCIP.
# نکتهٔ بازتولید: شناسهٔ scope از کل بایت‌های همین فایل ساخته می‌شود؛ تغییر توضیحات نیز آن را عوض می‌کند.
# گواه‌ها و برش‌های نسخه‌های قبلی باید در همین نسخه دوباره تولید شوند تا شناسهٔ منبع سازگار باشد.
# ==============================================================================
# زبان مدل‌سازی بهینه‌سازی JuMP را برای تعریف مدل، متغیر و قید بارگذاری می‌کند.
using JuMP
# رابط استاندارد وضعیت حل، جهت هدف و انواع قیود را با نام کوتاه MOI وارد می‌کند.
import MathOptInterface as MOI
# رابط حل‌کنندهٔ HiGHS را برای حل LP و MILP بارگذاری می‌کند.
using HiGHS
# کتابخانهٔ استاندارد اعداد تصادفی را بارگذاری می‌کند؛ بارگذاری آن سناریویی تولید نمی‌کند.
using Random
# کتابخانهٔ آمار جولیا را برای توابع آماری بارگذاری می‌کند.
using Statistics
# امکان قالب‌بندی خروجی متنی را بارگذاری می‌کند.
# توابع جبر خطی از جمله ضرب داخلی بردارها را بارگذاری می‌کند.
using LinearAlgebra
# آستانهٔ شکاف نسبی حل را ۰٫۰۰۱ قرار می‌دهد؛ این عدد به‌تنهایی گواه همگرایی افق کامل نیست.
const rddp_gap_tol   = 0.001
# سقف تکرار تنظیم‌شده در متغیر محیطی REVCS_ITERS را می‌خواند؛ پیش‌فرض ۳۸ یک تنظیم اجراست.
const rddp_max_iters = 38 # legacy display-only; plan iterations from validated CLI
# گام ۲۰ را برای حالت اختیاری discrete_step20 نگه می‌دارد؛ دقت شبکهٔ حالت جدید جداگانه و صریح تعیین می‌شود.
const disc_step_kw   = 20.0

# Gate 7.2: the ONLY source of runtime physics/economics is validated CLI.
# There are no ENV reads, silent paper sigma/delta-p defaults, or shared mutable data tables.
const G7_ACTIVE = Ref{Any}(nothing)
const G7_VERBOSE = Ref(false)
g7_load_log(x) = G7_VERBOSE[] ? println(x) : nothing
g7cfg() = G7_ACTIVE[] === nothing ? error(\"Gate7 runtime configuration not selected; use parse_gate7_cli\") : G7_ACTIVE[]
# Only a directly launched CLI run can request verbose output while the module loads.
# Includes from tests remain quiet and do not import SCIP.
if abspath(PROGRAM_FILE)==abspath(@__FILE__)
    G7_VERBOSE[] = any(==(\"--verbose=true\"),ARGS)
end

# The import happens only at the plan entrypoint; never in a method that
# immediately constructs a JuMP model (avoids Julia world-age failures).
function g7_load_scip_for_plan!()
    Base.find_package(\"SCIP\") === nothing &&
        error(\"SCIP is required for a three-stage plan; check/audit/root-only tests use HiGHS\")
    if !isdefined(@__MODULE__, :SCIP)
        @eval import SCIP
    end
    return nothing
end

function g7_scip_optimizer()
    isdefined(@__MODULE__, :SCIP) ||
        error(\"SCIP is not loaded. Run g7_load_scip_for_plan!() at the plan entrypoint, then enter the solver through Base.invokelatest\")
    return getproperty(getfield(@__MODULE__, :SCIP), :Optimizer)
end

function g7_read_topology(path::AbstractString)
    isfile(path) || error(\"--line-status-file not found: \" * path)
    status=fill(-1,37)
    for line in eachline(path)
        x=strip(line)
        (isempty(x) || startswith(x,\"#\") || startswith(lowercase(x),\"line_id\")) && continue
        fields=split(x)
        length(fields)==2 || error(\"Topology must contain exactly line_id and closed columns\")
        i=tryparse(Int,fields[1]); v=tryparse(Int,fields[2])
        (i!==nothing && 1<=i<=37 && v!==nothing && v in (0,1)) || error(\"Invalid topology row: \" * x)
        status[i]==-1 || error(\"Duplicate topology line ID: \" * string(i))
        status[i]=v
    end
    all(x->x in (0,1),status) || error(\"Topology must define all 37 unique lines\")
    # 32 closed edges on the 33-bus connected graph is a tree.
    adj=[Int[] for _ in 1:33]
    for l in 1:37
        if status[l]==1
            push!(adj[from_bus[l]],to_bus[l]);push!(adj[to_bus[l]],from_bus[l])
        end
    end
    visited=Set([1]); queue=[1]
    while !isempty(queue)
        i=popfirst!(queue)
        for j in adj[i]
            if !(j in visited)
                push!(visited,j);push!(queue,j)
            end
        end
    end
    connected=length(visited)==33
    radial=connected && sum(status)==32
    (connected && radial) || error(\"Gate 6.4 comparable topology requires a connected radial 33-bus graph with exactly 32 closed and 5 open lines; connected=\$connected closed=\$(sum(status))\")
    return (;status,connected,radial,closed=sum(status),open=37-sum(status),
        vector_hash=bytes2hex(sha256(join(status,\",\"))),
        file_hash=bytes2hex(sha256(read(path))),path=abspath(path))
end

const G7_PLAN_REQUIRED = Set((\"initial-state\",\"charging-step\",\"storage-step\",\"pv-step\",\"capacity\",
    \"sigma\",\"delta-p\",\"ope-scale\",\"line-status-file\",\"voltage-base-kv\",
    \"bess-power-policy\",\"soc-boundary\"))
const G7_PLAN_OPTIONAL = Set((\"mode\",\"output\",\"verbose\",\"iterations\",\"ccg-iterations\",\"cut-iterations\",
    \"seconds\",\"gap\",\"feasibility-repairs\",\"repair-mode\",\"forward-accept\",\"threads\",
    \"soc-initial-frac\",\"soc-terminal-frac\",\"soc-min-frac\",\"soc-max-frac\",\"sizing\"))
const G7_ENUMS = Dict(\"initial-state\"=>(\"paper_zero\",\"existing_five\"),
    \"capacity\"=>(\"printed_eq33\",\"installed_capacity\"),
    \"soc-boundary\"=>(\"cyclic_free_e0\",\"fractions\",\"continuous_96h\"),
    \"bess-power-policy\"=>(\"fixed_20kw\",\"scaled_half_Ce\"),
    \"repair-mode\"=>(\"nogood\",\"witness\"),
    \"forward-accept\"=>(\"optimal\",\"feasible_diagnostic\"),
    \"sizing\"=>(\"continuous\",\"discrete_step20\"))

function parse_gate7_cli(args)
    opts=Dict{String,String}()
    for arg in args
        startswith(arg,\"--\") && occursin(\"=\",arg) || error(\"Gate7 CLI requires --name=value: \" * arg)
        parts=split(arg[3:end],\"=\";limit=2)
        key,val=String(parts[1]),String(parts[2])
        isempty(strip(val)) && error(\"Gate7 CLI empty value --\" * key)
        haskey(opts,key) && error(\"Gate7 CLI duplicate --\" * key)
        opts[key]=val
    end
    mode=get(opts,\"mode\",\"check\")
    mode in (\"check\",\"initial-state-audit\",\"equivalence-report\",\"plan\") || error(\"Gate7 CLI unknown mode: \" * mode)
    allowed=mode==\"check\" ? Set((\"mode\",\"verbose\")) :
        mode==\"initial-state-audit\" ? Set((\"mode\",\"output\",\"verbose\")) :
        mode==\"equivalence-report\" ? union(G7_PLAN_REQUIRED,Set((\"mode\",\"output\",\"verbose\",\"soc-initial-frac\",
            \"soc-terminal-frac\",\"soc-min-frac\",\"soc-max-frac\",\"threads\",\"sizing\"))) :
        union(G7_PLAN_REQUIRED,G7_PLAN_OPTIONAL)
    extra=setdiff(Set(keys(opts)),allowed)
    isempty(extra) || error(\"Gate7 CLI forbidden/unknown flags for mode=\$mode: \" * join(sort!(collect(extra)),\",\"))
    if mode in (\"plan\",\"equivalence-report\")
        missing=setdiff(G7_PLAN_REQUIRED,Set(keys(opts)))
        isempty(missing) || error(\"Gate7 CLI missing mandatory flags: \" * join(sort!(collect(missing)),\",\"))
    end
    if haskey(opts,\"verbose\")
        opts[\"verbose\"] in (\"true\",\"false\") || error(\"--verbose must be true or false\")
    end
    for (key,values) in G7_ENUMS
        haskey(opts,key) && !(opts[key] in values) && error(\"Gate7 CLI invalid --\"*key*\"=\"*opts[key])
    end
    for key in (\"charging-step\",\"storage-step\",\"pv-step\",\"sigma\",\"delta-p\",\"ope-scale\",
            \"voltage-base-kv\",\"seconds\",\"gap\",\"soc-initial-frac\",\"soc-terminal-frac\",\"soc-min-frac\",\"soc-max-frac\")
        haskey(opts,key) || continue
        v=tryparse(Float64,opts[key]);(v!==nothing && isfinite(v)) || error(\"Gate7 CLI nonfinite/non-numeric --\" * key)
        if key in (\"charging-step\",\"storage-step\",\"pv-step\",\"delta-p\",\"voltage-base-kv\",\"seconds\")
            v>0 || error(\"Gate7 CLI --\"*key*\" must be > 0\")
        elseif key in (\"sigma\",\"ope-scale\")
            v>=0 || error(\"Gate7 CLI --\"*key*\" must be >= 0\")
        elseif key==\"gap\"
            0<=v<1 || error(\"Gate7 CLI --gap must be in [0,1)\")
        else
            0<=v<=1 || error(\"Gate7 CLI --\"*key*\" must be in [0,1]\")
        end
    end
    for key in (\"iterations\",\"ccg-iterations\",\"cut-iterations\",\"threads\",\"feasibility-repairs\")
        haskey(opts,key) || continue
        v=tryparse(Int,opts[key]);v!==nothing || error(\"Gate7 CLI invalid integer --\"*key)
        (key==\"feasibility-repairs\" ? v>=0 : v>0) || error(\"Gate7 CLI --\"*key*\" invalid range\")
    end
    if mode in (\"plan\",\"equivalence-report\")
        policy=opts[\"soc-boundary\"]
        if policy in (\"fractions\",\"continuous_96h\")
            all(haskey(opts,k) for k in (\"soc-initial-frac\",\"soc-terminal-frac\")) ||
                error(\"--soc-boundary=\$policy requires --soc-initial-frac and --soc-terminal-frac\")
        elseif any(haskey(opts,k) for k in (\"soc-initial-frac\",\"soc-terminal-frac\"))
            error(\"--soc-boundary=cyclic_free_e0 forbids fixed initial/terminal fractions\")
        end
        minf=parse(Float64,get(opts,\"soc-min-frac\",\"0.0\"));maxf=parse(Float64,get(opts,\"soc-max-frac\",\"1.0\"))
        minf<=maxf || error(\"SOC lower fraction exceeds upper\")
        if policy!=\"cyclic_free_e0\"
            minf<=parse(Float64,opts[\"soc-initial-frac\"])<=maxf || error(\"SOC initial outside bounds\")
            minf<=parse(Float64,opts[\"soc-terminal-frac\"])<=maxf || error(\"SOC terminal outside bounds\")
        end
        # BinaryGrid requires integer endpoint coverage; fail in the CLI and
        # record REVCS19_G7_INPUT_ERROR.log rather than failing after mkdir.
        for (key,maximum) in ((\"charging-step\",Cc_max),(\"storage-step\",Ce_max),(\"pv-step\",Cv_max))
            v=parse(Float64,opts[key]); q=maximum/v
            (isfinite(q) && 1.0<=q<=1.0e9 && isapprox(q,round(q);atol=1e-8,rtol=1e-10)) ||
                error(\"Gate7 CLI --\"*key*\" must divide the corresponding capacity maximum exactly: \" *
                    string(maximum)*\" / \"*string(v)*\" is not an integer\")
        end
        if opts[\"initial-state\"]==\"paper_zero\" && opts[\"capacity\"]==\"printed_eq33\"
            error(\"ALGEBRAICALLY INFEASIBLE: paper_zero has Cc[a,0]=0; Eq40 forbids simultaneous construction/expansion, so Ec[a,1]=0; printed Eq33 implies Pcs[a,1,tau]=0, contradicting positive EV demand Eq34. Use --capacity=installed_capacity for sensitivity, or existing_five+printed_eq33 for paper case study.\")
        end
        topology=g7_read_topology(opts[\"line-status-file\"])
        cfg=(;source=\"user_selected_not_published\",sigma=parse(Float64,opts[\"sigma\"]),
            delta_p=parse(Float64,opts[\"delta-p\"]),ope_scale=parse(Float64,opts[\"ope-scale\"]),
            voltage_base_kv=parse(Float64,opts[\"voltage-base-kv\"]),topology,
            bess_power_policy=Symbol(opts[\"bess-power-policy\"]),soc_boundary=Symbol(policy),
            soc_min=minf,soc_max=maxf,
            soc_initial=policy==\"cyclic_free_e0\" ? nothing : parse(Float64,opts[\"soc-initial-frac\"]),
            soc_terminal=policy==\"cyclic_free_e0\" ? nothing : parse(Float64,opts[\"soc-terminal-frac\"]),
            threads=parse(Int,get(opts,\"threads\",\"8\")),
            sizing=Symbol(get(opts,\"sizing\",\"continuous\")),
            initial_state=opts[\"initial-state\"],capacity_mode=Symbol(opts[\"capacity\"]))
        return (;mode,opts,cfg)
    end
    return (;mode,opts,cfg=nothing)
end

function g7_scope_fields()
    c=g7cfg()
    return (c.initial_state,c.capacity_mode,c.sigma,c.delta_p,c.ope_scale,c.voltage_base_kv,
        c.topology.vector_hash,c.bess_power_policy,c.soc_boundary,c.soc_min,c.soc_max,
        c.soc_initial,c.soc_terminal,c.sizing,Tuple(theta_fc),Tuple(theta_err),
        Tuple(zeta_fc),Tuple(zeta_err),CHARGING_ASSIGNMENT_MODE,LINE1_MODE,
        Tuple(candidate_roads),MODEL_SOURCE_HASH)
end
function g7_scope_metadata()
    c=g7cfg()
    return Dict{String,Any}(
        \"initial_state_scenario\"=>c.initial_state,
        \"initial_state_role\"=>c.initial_state==\"existing_five\" ? \"paper_case_study_baseline\" : \"literal_eq37_text_sensitivity\",
        \"sigma\"=>c.sigma,\"delta_p\"=>c.delta_p,\"ope_scale\"=>c.ope_scale,
        \"economic_assumption_provenance\"=>\"USER_SELECTED_NOT_PUBLISHED\",
        \"voltage_base_kv\"=>c.voltage_base_kv,
        \"line_status_file\"=>c.topology.path,\"topology_hash\"=>c.topology.vector_hash,
        \"topology_file_sha256\"=>c.topology.file_hash,\"topology_connected\"=>c.topology.connected,
        \"topology_radial\"=>c.topology.radial,\"closed_lines\"=>c.topology.closed,
        \"open_lines\"=>c.topology.open,
        \"bess_power_policy\"=>string(c.bess_power_policy),
        \"soc_boundary\"=>string(c.soc_boundary),\"soc_min_frac\"=>c.soc_min,\"soc_max_frac\"=>c.soc_max,
        \"soc_initial_frac\"=>c.soc_initial===nothing ? \"free_day_start\" : c.soc_initial,
        \"soc_terminal_frac\"=>c.soc_terminal===nothing ? \"same_free_day_start\" : c.soc_terminal,
        \"sizing\"=>string(c.sizing),\"upper_approximation_variant\"=>\"certified_codebook_upper\",
        \"model_type\"=>\"finite_state_grid_discretization\",
        \"rddp_global_feasibility_certificate\"=>\"BLOCKED\",
        \"full_paper_reproduction\"=>false,
        \"traffic_period2_factor_range\"=>[1+theta_fc[2]-theta_err[2],1+theta_fc[2]+theta_err[2]],
        \"traffic_period3_factor_range\"=>[1+theta_fc[3]-theta_err[3],1+theta_fc[3]+theta_err[3]],
        \"dre_period2_factor_range\"=>[1+zeta_fc[2]-zeta_err[2],1+zeta_fc[2]+zeta_err[2]],
        \"dre_period3_factor_range\"=>[1+zeta_fc[3]-zeta_err[3],1+zeta_fc[3]+zeta_err[3]])
end

# تابع ساخت مدل JuMP با حل‌کنندهٔ HiGHS و تنظیم زمان و شکاف حل را تعریف می‌کند.
function create_highs_model(; silent::Bool = true, gap::Float64 = rddp_gap_tol, time_lim::Float64 = 600.0)
    # مدل جدید JuMP را با حل‌کنندهٔ HiGHS ایجاد می‌کند.
    m = Model(HiGHS.Optimizer)
    # پیش‌پردازش مدل را در HiGHS فعال می‌کند.
    set_optimizer_attribute(m, \"presolve\", \"on\")
    # تعداد رشته‌های محاسباتی HiGHS را ۸ تنظیم می‌کند؛ این عدد تنظیم اجراست.
    set_optimizer_attribute(m, \"threads\", g7cfg().threads)
    # شکاف نسبی مجاز MILP را به حل‌کننده می‌دهد.
    set_optimizer_attribute(m, \"mip_rel_gap\", gap)
    # مهلت حل این مدل را بر حسب ثانیه اعمال می‌کند.
    set_optimizer_attribute(m, \"time_limit\", time_lim)
    # نمایش خروجی حل‌کننده را بر اساس حالت سکوت کنترل می‌کند.
    set_optimizer_attribute(m, \"output_flag\", !silent)
    # مدل ساخته‌شده یا تنظیم‌شده را برای استفادهٔ فراخواننده برمی‌گرداند.
    return m
# تعریف تابع create_highs_model را پایان می‌دهد.
end
# پایان بارگذاری کتابخانه‌ها و تنظیمات پایه را در خروجی اعلام می‌کند.
g7_load_log(\"✅ [Part 1] Packages, MOI interface, and Improved RDDP parameters initialized.\")
# تعداد دوره‌های برنامه‌ریزی را برابر ۳ تعریف می‌کند.
const num_periods     = 3
# چهار روز نمونه را برای هر دوره در نظر می‌گیرد.
const num_days        = 4
# تعداد ساعت‌های هر روز نمونه را ۲۴ تعیین می‌کند.
const hours_day       = 24
# تعداد بازه‌های ساعتی هر دوره را از حاصل‌ضرب روزها در ساعت‌های روز به دست می‌آورد.
const num_tau         = num_days * hours_day
# تعداد کل بازه‌های ساعتی سه دوره را محاسبه می‌کند؛ وزن سالانه‌ای به این عدد اضافه نمی‌شود.
const num_total_hours = num_periods * num_tau
# تعداد شین‌های شبکهٔ توزیع برق را ۳۳ تعریف می‌کند.
const num_buses       = 33
# تعداد گره‌های شبکهٔ حمل‌ونقل را ۱۲ تعریف می‌کند.
const num_utn_nodes   = 12
# تعداد جاده‌های شبکهٔ حمل‌ونقل را ۲۰ تعریف می‌کند.
const num_roads       = 20
# تعداد جفت‌های مبدأ و مقصد تقاضای سفر را ۹ تعیین می‌کند.
const num_OD_pairs    = 9
# تعداد مسیرهای انتخابی برای هر جفت مبدأ و مقصد را ۳ تعیین می‌کند.
const num_paths       = 3
# تعداد خطوط برق، شامل ۳۲ شاخهٔ اصلی و ۵ خط رابط، را ۳۷ تعریف می‌کند.
const num_lines       = 37
# تعداد واحدهای بادی شبکهٔ برق را ۵ تعیین می‌کند.
const num_wt          = 5
# تعداد واحدهای خورشیدی متصل به شبکهٔ برق را ۵ تعیین می‌کند.
const num_pv_pdn      = 5
# تعداد کل واحدهای تجدیدپذیر شبکهٔ برق را جمع می‌کند.
const num_dre         = num_wt + num_pv_pdn
# مجموعهٔ اندیس دوره‌های برنامه‌ریزی را می‌سازد.
const T_set           = 1:num_periods
# مجموعهٔ اندیس چهار روز نمونه را می‌سازد.
const Day_set         = 1:num_days
# مجموعهٔ اندیس ساعت‌های یک روز را می‌سازد.
const Hour_set        = 1:hours_day
# مجموعهٔ اندیس ۹۶ بازهٔ ساعتی یک دوره را می‌سازد.
const Tau_set         = 1:num_tau
# مجموعهٔ شمارهٔ شین‌های برق را تعریف می‌کند.
const I_set           = 1:num_buses
# مجموعهٔ شین‌های دارای بار در مدل فعلی را تعریف می‌کند.
const D_set           = 1:num_buses
# مجموعهٔ تمام جاده‌های شبکهٔ حمل‌ونقل را تعریف می‌کند.
const B_set           = 1:num_roads
# حالت انتخاب محل‌های کاندید ایستگاه را روی تمام ۲۰ جاده قرار می‌دهد.
const CANDIDATE_MODE  = :all_20
# طبق حالت انتخاب، فهرست جاده‌های کاندید را می‌سازد؛ فهرست جایگزین فقط یک گزینهٔ پیکربندی است.
const candidate_roads = (CANDIDATE_MODE == :all_20) ? collect(1:num_roads) : [1, 2, 3, 4, 7, 8, 10, 11, 12, 14, 16]
# مجموعهٔ محل‌های مجاز احداث و توسعهٔ ایستگاه را از فهرست کاندیدها می‌گیرد.
const A_set           = candidate_roads
# تعداد محل‌های کاندید ایستگاه را محاسبه می‌کند.
const num_candidates  = length(A_set)
# مجموعهٔ اندیس جفت‌های مبدأ و مقصد را می‌سازد.
const OD_set          = 1:num_OD_pairs
# مجموعهٔ اندیس مسیرهای انتخابی هر جفت مبدأ و مقصد را می‌سازد.
const K_set           = 1:num_paths
# مجموعهٔ اندیس خطوط برق را می‌سازد.
const L_set           = 1:num_lines
# شین ۱ را به‌عنوان محل پست بالادست ثبت می‌کند.
const U_set           = [1]
# مجموعهٔ اندیس واحدهای بادی را تعریف می‌کند.
const WT_set          = 1:num_wt
# مجموعهٔ اندیس واحدهای خورشیدی شبکهٔ برق را تعریف می‌کند.
const PV_PDN_set      = 1:num_pv_pdn
# مجموعهٔ اندیس تمام واحدهای تجدیدپذیر شبکهٔ برق را تعریف می‌کند.
const R_set           = 1:num_dre
# هر اندیس ساعتی ۱ تا ۹۶ را با تقسیم صحیح به شمارهٔ روز نمونه نگاشت می‌کند.
const day_of_tau      = [div(tau - 1, hours_day) + 1 for tau in Tau_set]
# با باقیماندهٔ تقسیم، ساعت شبانه‌روز متناظر با هر بازه را محاسبه می‌کند.
const hour_of_tau     = [mod(tau - 1, hours_day) + 1 for tau in Tau_set]
# شمارهٔ شین اتصال پنج واحد بادی را از دادهٔ موجود ثبت می‌کند.
const wt_buses        = [4, 13, 22, 27, 31]
# شمارهٔ شین اتصال پنج واحد خورشیدی شبکه را از دادهٔ موجود ثبت می‌کند.
const pv_pdn_buses    = [7, 11, 17, 19, 25]
# محل اتصال واحدهای بادی و خورشیدی شبکه را در یک بردار ادغام می‌کند.
const dre_buses       = vcat(wt_buses, pv_pdn_buses)
# نگاشت هر یک از ۲۰ جاده به شین برق محل اتصال ایستگاه همان جاده را ثبت می‌کند.
const road_to_bus     = [3, 4, 5, 29, 7, 14, 18, 10, 19, 12, 13, 8, 15, 16, 17, 33, 32, 23, 21, 26]
# برای نگاشت ایستگاه به شین، همان نگاشت جاده به شین را به کار می‌برد.
const station_to_bus  = road_to_bus
# نگاشت جاده‌های واقعاً کاندید به شین برق را در یک فرهنگ داده ذخیره می‌کند.
const candidate_road_to_bus = Dict(a => road_to_bus[a] for a in A_set)
# فهرست دو سر جاده‌های حمل‌ونقل را آغاز می‌کند؛ جست‌وجوی مسیر این گراف را بدون جهت به کار می‌برد.
const utn_road_edges = [
    # جادهٔ R1 را بین گره‌های T1 و T3 ثبت می‌کند.
    (1, 3),
    # جادهٔ R2 را بین گره‌های T1 و T2 ثبت می‌کند.
    (1, 2),
    # جادهٔ R3 را بین گره‌های T2 و T6 ثبت می‌کند.
    (2, 6),
    # جادهٔ R4 را بین گره‌های T1 و T4 ثبت می‌کند.
    (1, 4),
    # جادهٔ R5 را بین گره‌های T2 و T5 ثبت می‌کند.
    (2, 5),
    # جادهٔ R6 را بین گره‌های T3 و T4 ثبت می‌کند.
    (3, 4),
    # جادهٔ R7 را بین گره‌های T4 و T5 ثبت می‌کند.
    (4, 5),
    # جادهٔ R8 را بین گره‌های T5 و T6 ثبت می‌کند.
    (5, 6),
    # جادهٔ R9 را بین گره‌های T3 و T7 ثبت می‌کند.
    (3, 7),
    # جادهٔ R10 را بین گره‌های T4 و T8 ثبت می‌کند.
    (4, 8),
    # جادهٔ R11 را بین گره‌های T5 و T9 ثبت می‌کند.
    (5, 9),
    # جادهٔ R12 را بین گره‌های T6 و T10 ثبت می‌کند.
    (6, 10),
    # جادهٔ R13 را بین گره‌های T7 و T8 ثبت می‌کند.
    (7, 8),
    # جادهٔ R14 را بین گره‌های T8 و T9 ثبت می‌کند.
    (8, 9),
    # جادهٔ R15 را بین گره‌های T9 و T10 ثبت می‌کند.
    (9, 10),
    # جادهٔ R16 را بین گره‌های T7 و T11 ثبت می‌کند.
    (7, 11),
    # جادهٔ R17 را بین گره‌های T8 و T11 ثبت می‌کند.
    (8, 11),
    # جادهٔ R18 را بین گره‌های T9 و T12 ثبت می‌کند.
    (9, 12),
    # جادهٔ R19 را بین گره‌های T10 و T12 ثبت می‌کند.
    (10, 12),
    # جادهٔ R20 را بین گره‌های T11 و T12 ثبت می‌کند.
    (11, 12)
# تعریف جدول یا بردار utn_road_edges را تکمیل می‌کند.
]
# جدول جفت گره‌های مبدأ و مقصد تقاضای سفر را آغاز می‌کند.
const od_node_pairs = [
    # جفت سفر شمارهٔ 1 را از گرهٔ T1 به گرهٔ T6 ثبت می‌کند.
    (1, 6),
    # جفت سفر شمارهٔ 2 را از گرهٔ T1 به گرهٔ T10 ثبت می‌کند.
    (1, 10),
    # جفت سفر شمارهٔ 3 را از گرهٔ T1 به گرهٔ T12 ثبت می‌کند.
    (1, 12),
    # جفت سفر شمارهٔ 4 را از گرهٔ T3 به گرهٔ T6 ثبت می‌کند.
    (3, 6),
    # جفت سفر شمارهٔ 5 را از گرهٔ T3 به گرهٔ T12 ثبت می‌کند.
    (3, 12),
    # جفت سفر شمارهٔ 6 را از گرهٔ T3 به گرهٔ T11 ثبت می‌کند.
    (3, 11),
    # جفت سفر شمارهٔ 7 را از گرهٔ T4 به گرهٔ T9 ثبت می‌کند.
    (4, 9),
    # جفت سفر شمارهٔ 8 را از گرهٔ T4 به گرهٔ T10 ثبت می‌کند.
    (4, 10),
    # جفت سفر شمارهٔ 9 را از گرهٔ T4 به گرهٔ T12 ثبت می‌کند.
    (4, 12)
# تعریف جدول یا بردار od_node_pairs را تکمیل می‌کند.
]
# تعریف توپولوژی برق، حمل‌ونقل و نگاشت اتصال دو شبکه را در خروجی اعلام می‌کند.
g7_load_log(\"✅ [Part 2] 33P-12U topology, coupling buses, and 12-node UTN graph structure defined.\")
# بردار ظرفیت جاده‌ها بر حسب خودرو در ساعت را آغاز می‌کند.
const phi_b = [
    # ظرفیت جادهٔ R1 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3528.00,
    # ظرفیت جادهٔ R2 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3920.00,
    # ظرفیت جادهٔ R3 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3332.00,
    # ظرفیت جادهٔ R4 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1920.80,
    # ظرفیت جادهٔ R5 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1548.40,
    # ظرفیت جادهٔ R6 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1666.00,
    # ظرفیت جادهٔ R7 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    2646.00,
    # ظرفیت جادهٔ R8 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1607.20,
    # ظرفیت جادهٔ R9 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3724.00,
    # ظرفیت جادهٔ R10 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    2744.00,
    # ظرفیت جادهٔ R11 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    2704.80,
    # ظرفیت جادهٔ R12 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3920.00,
    # ظرفیت جادهٔ R13 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1744.40,
    # ظرفیت جادهٔ R14 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    2587.20,
    # ظرفیت جادهٔ R15 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1792.00,
    # ظرفیت جادهٔ R16 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3430.00,
    # ظرفیت جادهٔ R17 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1912.40,
    # ظرفیت جادهٔ R18 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    1758.40,
    # ظرفیت جادهٔ R19 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3567.20,
    # ظرفیت جادهٔ R20 را بر حسب خودرو در ساعت از دادهٔ موجود ثبت می‌کند.
    3920.00
# تعریف جدول یا بردار phi_b را تکمیل می‌کند.
]
# بردار زمان سفر آزاد جاده‌ها بر حسب دقیقه را آغاز می‌کند.
const h0_b = [
     # زمان سفر آزاد جادهٔ R1 را بر حسب دقیقه ثبت می‌کند.
     6.0,
    # زمان سفر آزاد جادهٔ R2 را بر حسب دقیقه ثبت می‌کند.
    10.0,
     # زمان سفر آزاد جادهٔ R3 را بر حسب دقیقه ثبت می‌کند.
     6.5,
     # زمان سفر آزاد جادهٔ R4 را بر حسب دقیقه ثبت می‌کند.
     5.0,
     # زمان سفر آزاد جادهٔ R5 را بر حسب دقیقه ثبت می‌کند.
     5.5,
     # زمان سفر آزاد جادهٔ R6 را بر حسب دقیقه ثبت می‌کند.
     6.0,
    # زمان سفر آزاد جادهٔ R7 را بر حسب دقیقه ثبت می‌کند.
    12.0,
     # زمان سفر آزاد جادهٔ R8 را بر حسب دقیقه ثبت می‌کند.
     6.5,
    # زمان سفر آزاد جادهٔ R9 را بر حسب دقیقه ثبت می‌کند.
    10.2,
    # زمان سفر آزاد جادهٔ R10 را بر حسب دقیقه ثبت می‌کند.
    11.5,
    # زمان سفر آزاد جادهٔ R11 را بر حسب دقیقه ثبت می‌کند.
    12.5,
    # زمان سفر آزاد جادهٔ R12 را بر حسب دقیقه ثبت می‌کند.
    10.5,
     # زمان سفر آزاد جادهٔ R13 را بر حسب دقیقه ثبت می‌کند.
     5.8,
    # زمان سفر آزاد جادهٔ R14 را بر حسب دقیقه ثبت می‌کند.
    11.0,
     # زمان سفر آزاد جادهٔ R15 را بر حسب دقیقه ثبت می‌کند.
     5.9,
     # زمان سفر آزاد جادهٔ R16 را بر حسب دقیقه ثبت می‌کند.
     6.3,
     # زمان سفر آزاد جادهٔ R17 را بر حسب دقیقه ثبت می‌کند.
     5.7,
     # زمان سفر آزاد جادهٔ R18 را بر حسب دقیقه ثبت می‌کند.
     5.8,
     # زمان سفر آزاد جادهٔ R19 را بر حسب دقیقه ثبت می‌کند.
     6.1,
     # زمان سفر آزاد جادهٔ R20 را بر حسب دقیقه ثبت می‌کند.
     9.8
# تعریف جدول یا بردار h0_b را تکمیل می‌کند.
]
# دادهٔ مکمل Table 1: پنج REVCS موجود در سال پایه روی جاده‌های R2، R3، R10، R14 و R16.
# این بردار «واقعیت جدول مکمل» است و به‌تنهایی انتخاب مبنای اولیهٔ مدل را تعیین نمی‌کند.
const existing_REVCS = zeros(Int, num_roads)
for road_idx in [2, 3, 10, 14, 16]
    existing_REVCS[road_idx] = 1
end
# دو شاخهٔ مستقل وضعیت اولیه؛ paper_zero دقیقاً از z[a,0]=0 و C[a,0]=0 مقاله پیروی می‌کند.
const INITIAL_STATE_SCENARIOS = (\"paper_zero\", \"existing_five\")
function initial_station_vector(scenario::AbstractString)
    scenario == \"paper_zero\" && return zeros(Int, num_roads)
    scenario == \"existing_five\" && return copy(existing_REVCS)
    error(\"initial-state must be exactly paper_zero or existing_five\")
end
# ظرفیت پایهٔ پنج واحد بادی را بر حسب کیلووات ثبت می‌کند.
const wt_capacities = [263.50, 395.00, 395.00, 197.50, 461.00]
# ظرفیت پایهٔ پنج واحد خورشیدی شبکه را بر حسب کیلووات ثبت می‌کند.
const pv_pdn_capacities = [253.00, 184.00, 276.50, 138.00, 322.50]
# ظرفیت پایهٔ تمام منابع تجدیدپذیر شبکهٔ برق را کنار هم قرار می‌دهد.
const Der_g1 = vcat(wt_capacities, pv_pdn_capacities)
# جدول خروجی نرمال‌شدهٔ باد را آغاز می‌کند؛ سطرها ساعت و چهار ستون، روزهای نمونه هستند.
const wt_pu_matrix = [
    # خروجی بادی نرمال‌شدهٔ ساعت 1 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.8588  0.8520  0.8481  0.8448;
    # خروجی بادی نرمال‌شدهٔ ساعت 2 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.8458  0.8381  0.8372  1.0000;
    # خروجی بادی نرمال‌شدهٔ ساعت 3 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7924  0.8957  0.8522  0.8887;
    # خروجی بادی نرمال‌شدهٔ ساعت 4 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6601  0.6704  0.7389  0.5758;
    # خروجی بادی نرمال‌شدهٔ ساعت 5 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6009  0.6534  0.6621  0.5688;
    # خروجی بادی نرمال‌شدهٔ ساعت 6 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7847  0.7136  0.8577  0.6335;
    # خروجی بادی نرمال‌شدهٔ ساعت 7 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6124  0.6442  0.6007  0.6831;
    # خروجی بادی نرمال‌شدهٔ ساعت 8 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6896  0.5872  0.6726  0.7205;
    # خروجی بادی نرمال‌شدهٔ ساعت 9 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.5393  0.5263  0.5964  0.5916;
    # خروجی بادی نرمال‌شدهٔ ساعت 10 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6109  0.5272  0.5340  0.5445;
    # خروجی بادی نرمال‌شدهٔ ساعت 11 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.4547  0.4455  0.5373  0.4693;
    # خروجی بادی نرمال‌شدهٔ ساعت 12 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.4324  0.3816  0.4442  0.4655;
    # خروجی بادی نرمال‌شدهٔ ساعت 13 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.5005  0.5012  0.4932  0.4883;
    # خروجی بادی نرمال‌شدهٔ ساعت 14 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.4435  0.4446  0.4271  0.4159;
    # خروجی بادی نرمال‌شدهٔ ساعت 15 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.4701  0.4660  0.4064  0.4484;
    # خروجی بادی نرمال‌شدهٔ ساعت 16 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.4992  0.4726  0.4543  0.5192;
    # خروجی بادی نرمال‌شدهٔ ساعت 17 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.5410  0.5127  0.5210  0.4581;
    # خروجی بادی نرمال‌شدهٔ ساعت 18 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.4736  0.5237  0.4258  0.4602;
    # خروجی بادی نرمال‌شدهٔ ساعت 19 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6532  0.6919  0.6954  0.5859;
    # خروجی بادی نرمال‌شدهٔ ساعت 20 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7407  0.7837  0.7431  0.7010;
    # خروجی بادی نرمال‌شدهٔ ساعت 21 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7549  0.7233  0.7103  0.6786;
    # خروجی بادی نرمال‌شدهٔ ساعت 22 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7734  0.7204  0.7257  0.7012;
    # خروجی بادی نرمال‌شدهٔ ساعت 23 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.8414  0.7655  0.9142  0.8269;
    # خروجی بادی نرمال‌شدهٔ ساعت 24 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6960  0.7364  0.7508  0.6094
# تعریف جدول یا بردار wt_pu_matrix را تکمیل می‌کند.
]
# جدول باد را به ترتیب ستونی جولیا به بردار ۹۶ ساعتی تبدیل می‌کند.
const wt_profile = vec(wt_pu_matrix)
# جدول خروجی نرمال‌شدهٔ خورشید را آغاز می‌کند؛ سطرها ساعت و ستون‌ها روزهای نمونه هستند.
const pv_pu_matrix = [
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 1 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 2 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 3 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 4 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 5 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 6 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 7 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.1495  0.1309  0.1545  0.1497;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 8 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.4539  0.4829  0.4907  0.4471;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 9 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7976  0.7449  0.7228  0.7925;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 10 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.8365  0.7433  0.8568  0.8111;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 11 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.8365  0.9471  0.9049  0.8050;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 12 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.5854  0.6032  0.5801  0.5447;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 13 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.6320  0.6173  0.6019  0.6579;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 14 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7100  0.6858  0.6483  0.6458;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 15 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.9526  0.9114  0.7914  1.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 16 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.7700  0.8474  0.8300  0.8318;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 17 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.8675  0.8602  0.8063  0.9632;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 18 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.8088  0.7378  0.8746  0.7704;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 19 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.5153  0.5726  0.5725  0.5068;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 20 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.3538  0.3563  0.3661  0.3291;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 21 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 22 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 23 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000;
    # خروجی خورشیدی نرمال‌شدهٔ ساعت 24 را برای روزهای نمونهٔ اول تا چهارم ثبت می‌کند.
    0.0000  0.0000  0.0000  0.0000
# تعریف جدول یا بردار pv_pu_matrix را تکمیل می‌کند.
]
# جدول خورشیدی را به ترتیب روز اول تا چهارم به بردار ۹۶ ساعتی تبدیل می‌کند.
const pv_profile = vec(pv_pu_matrix)
# جدول تقاضای سفر روز نخست را آغاز می‌کند؛ سطرها ساعت و ۹ ستون، جفت‌های مبدأ و مقصد هستند.
const Df_day1_table = [
    # تقاضای سفر ساعت 1 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    558.88  688.21  783.89  766.87  851.40  417.42   872.69  750.69  505.26;
    # تقاضای سفر ساعت 2 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    498.51  566.25  937.52  797.87  812.26  520.54   878.34  674.65  520.45;
    # تقاضای سفر ساعت 3 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    557.05  701.05  857.45  660.37  867.99  542.61  1006.78  769.34  494.21;
    # تقاضای سفر ساعت 4 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    536.30  567.19  710.54  730.44  712.53  503.96   825.72  578.77  527.67;
    # تقاضای سفر ساعت 5 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    517.37  610.26  873.81  617.45  761.54  498.60   971.65  673.01  514.91;
    # تقاضای سفر ساعت 6 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    460.46  543.88  776.02  785.49  878.85  494.07   900.00  772.60  444.14;
    # تقاضای سفر ساعت 7 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    501.22  581.35  874.49  638.59  779.24  432.01   874.86  688.93  480.72;
    # تقاضای سفر ساعت 8 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    550.13  703.24  834.43  706.61  745.39  424.46   836.58  731.23  439.48;
    # تقاضای سفر ساعت 9 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    500.88  560.02  919.41  715.41  689.61  522.24   922.71  742.75  437.30;
    # تقاضای سفر ساعت 10 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    511.81  610.18  812.58  820.06  736.62  571.48  1022.81  680.23  547.11;
    # تقاضای سفر ساعت 11 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    425.77  508.37  769.34  788.10  843.90  461.13   827.25  674.86  421.16;
    # تقاضای سفر ساعت 12 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    488.33  567.57  795.04  731.88  863.26  499.23   937.99  620.42  485.07;
    # تقاضای سفر ساعت 13 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    562.87  641.87  787.79  653.38  731.54  528.54   874.87  755.18  552.29;
    # تقاضای سفر ساعت 14 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    501.21  589.32  853.83  662.79  922.20  451.49   978.38  681.19  494.84;
    # تقاضای سفر ساعت 15 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    503.18  559.43  798.52  752.81  781.37  496.79   857.54  599.31  484.41;
    # تقاضای سفر ساعت 16 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    443.50  624.35  806.49  679.25  716.55  567.49   988.93  609.26  534.21;
    # تقاضای سفر ساعت 17 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    536.92  541.77  697.29  623.58  798.96  487.10   892.18  569.52  574.63;
    # تقاضای سفر ساعت 18 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    508.93  581.53  818.08  720.55  875.49  488.72   898.31  726.70  516.36;
    # تقاضای سفر ساعت 19 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    485.71  578.51  775.14  677.81  851.99  569.09   855.15  570.80  450.45;
    # تقاضای سفر ساعت 20 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    500.93  628.45  785.22  579.14  686.29  483.14   984.78  707.47  542.84;
    # تقاضای سفر ساعت 21 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    512.17  598.03  893.31  701.43  842.22  508.93   858.59  721.66  508.43;
    # تقاضای سفر ساعت 22 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    438.12  634.90  918.74  758.52  818.60  491.59   837.34  714.12  469.08;
    # تقاضای سفر ساعت 23 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    509.93  579.14  818.08  707.48  912.95  492.19   822.95  772.18  578.51;
    # تقاضای سفر ساعت 24 روز نخست را به ترتیب ۹ جفت مبدأ و مقصد ثبت می‌کند.
    528.37  656.26  848.97  667.47  763.86  501.35   783.92  745.68  425.11
# تعریف جدول یا بردار Df_day1_table را تکمیل می‌کند.
]
# همان تقاضای روز نخست را برای چهار روز تکرار می‌کند؛ دادهٔ جدید روزانه تولید نمی‌کند.
const Df_initial = repeat(Df_day1_table, num_days, 1)

# جست‌وجوی بازگشتی تمام مسیرهای سادهٔ گراف حمل‌ونقل را تعریف می‌کند.
function find_all_simple_paths_roads(
    # آرگومان «شمارهٔ گره فعلی جست‌وجوی مسیر» را در امضای تابع مشخص می‌کند.
    u::Int,
    # آرگومان «گره مقصد جست‌وجوی مسیر» را در امضای تابع مشخص می‌کند.
    target::Int,
    # آرگومان «بردار نشان‌دهندهٔ گره‌های بازدیدشدهٔ مسیر فعلی» را در امضای تابع مشخص می‌کند.
    visited_nodes::Vector{Bool},
    # آرگومان «فهرست جاده‌های مسیر موقت» را در امضای تابع مشخص می‌کند.
    current_roads::Vector{Int},
    # آرگومان «محل انباشت تمام مسیرهای کامل» را در امضای تابع مشخص می‌کند.
    all_road_paths::Vector{Vector{Int}}
# عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
)
    # گره جاری را بازدیدشده علامت می‌زند تا مسیر ساده چرخه نداشته باشد.
    visited_nodes[u] = true
    # شرط رسیدن گره جاری به مقصد مسیر را بررسی می‌کند.
    if u == target
        # یک کپی مستقل از مسیر کامل پیدا‌شده را ذخیره می‌کند.
        push!(all_road_paths, copy(current_roads))
    # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
    else
        # همهٔ جاده‌ها را با شماره و دو سر آن‌ها برای پیدا کردن همسایهٔ گره جاری بررسی می‌کند.
        for (road_id, (n1, n2)) in enumerate(utn_road_edges)
            # همسایهٔ بعدی را ابتدا نامعتبر قرار می‌دهد.
            next_node = 0
            # شرط اتصال سر اول جاده به گره جاری و بازدیدنشدن سر دوم را بررسی می‌کند.
            if n1 == u && !visited_nodes[n2]
                # سر دوم جاده را به‌عنوان گره بعدی انتخاب می‌کند.
                next_node = n2
            # در غیر این صورت، شرط اتصال سر دوم جاده به گره جاری و بازدیدنشدن سر اول را بررسی می‌کند.
            elseif n2 == u && !visited_nodes[n1]
                # سر اول جاده را به‌عنوان گره بعدی انتخاب می‌کند.
                next_node = n1
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
            # شرط پیداشدن همسایهٔ مجاز برای ادامهٔ مسیر را بررسی می‌کند.
            if next_node > 0
                # جادهٔ انتخاب‌شده را به مسیر موقت اضافه می‌کند.
                push!(current_roads, road_id)
                # جست‌وجوی مسیر را به‌صورت بازگشتی از همسایه ادامه می‌دهد.
                find_all_simple_paths_roads(next_node, target, visited_nodes, current_roads, all_road_paths)
                # هنگام عقب‌گرد، آخرین جاده را از مسیر موقت حذف می‌کند.
                pop!(current_roads)
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # علامت بازدید گره را برای بررسی مسیرهای دیگر آزاد می‌کند.
    visited_nodes[u] = false
# تعریف تابع find_all_simple_paths_roads را پایان می‌دهد.
end

# استخراج مسیرهای دارای کمترین مجموع زمان آزاد و ماتریس وقوع جاده را تعریف می‌کند.
function compute_k_shortest_paths(od_pairs, num_k::Int, edge_weights::Vector{Float64})
    # تانسور صفر و یک وقوع جاده در هر مسیر و جفت مبدأ و مقصد را ایجاد می‌کند.
    lambda_mat = zeros(Int, length(od_pairs), num_k, length(edge_weights))
    # محل ذخیرهٔ فهرست مسیرهای هر جفت مبدأ و مقصد را تخصیص می‌دهد.
    extracted_paths = Vector{Vector{Vector{Int}}}(undef, length(od_pairs))
    # هر جفت مبدأ و مقصد را همراه شمارهٔ آن برای استخراج مسیرها پردازش می‌کند.
    for (rs, (orig, dest)) in enumerate(od_pairs)
        # فهرست مسیرهای سادهٔ جفت جاری را خالی آغاز می‌کند.
        all_paths = Vector{Vector{Int}}()
        # بردار بازدید گره‌ها را برای جست‌وجوی جدید صفر می‌کند.
        visited = fill(false, num_utn_nodes)
        # تمام مسیرهای سادهٔ بین مبدأ و مقصد جاری را استخراج می‌کند.
        find_all_simple_paths_roads(orig, dest, visited, Int[], all_paths)
        # هزینهٔ هر مسیر را از مجموع زمان آزاد جاده‌های آن محاسبه می‌کند.
        path_costs = [sum(edge_weights[road] for road in p) for p in all_paths]
        # ترتیب مسیرها را از کمترین به بیشترین زمان آزاد به دست می‌آورد.
        sorted_indices = sortperm(path_costs)
        # فهرست مسیرهای منتخب جفت جاری را آغاز می‌کند.
        selected_for_od = Vector{Vector{Int}}()
        # تا تعداد مسیر درخواستی یا تعداد مسیر موجود، هرکدام کمتر است، مسیر انتخاب می‌کند.
        for k in 1:min(num_k, length(sorted_indices))
            # مسیر دارای رتبهٔ جاری در ترتیب زمان آزاد را انتخاب می‌کند.
            best_path = all_paths[sorted_indices[k]]
            # مسیر انتخابی را به فهرست مسیرهای قابل استفاده اضافه می‌کند.
            push!(selected_for_od, best_path)
            # تمام جاده‌های مسیر انتخابی را برای تکمیل ماتریس وقوع پیمایش می‌کند.
            for road in best_path
                # حضور جادهٔ جاری در مسیر انتخابی را با یک ثبت می‌کند.
                lambda_mat[rs, k, road] = 1
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # مسیرهای انتخابی جفت مبدأ و مقصد جاری را ذخیره می‌کند.
        extracted_paths[rs] = selected_for_od
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # ماتریس وقوع جاده و فهرست خود مسیرها را برمی‌گرداند.
    return lambda_mat, extracted_paths
# تعریف تابع compute_k_shortest_paths را پایان می‌دهد.
end
# سه مسیر با کمترین مجموع زمان آزاد را محاسبه و ماتریس وقوع جاده در مسیر را استخراج می‌کند.
const Lambda_rskb, algorithmic_od_paths = compute_k_shortest_paths(od_node_pairs, num_paths, h0_b)
# ماتریس وقوع محل ایستگاه در مسیر را با همان وقوع جاده‌ها مقداردهی می‌کند.
const X_rska = copy(Lambda_rskb)
# آماده‌بودن پارامترهای جاده، پروفایل‌ها و مسیرهای محاسبه‌شده را اعلام می‌کند.
g7_load_log(\"✅ [Part 3 Complete] Road parameters, 96-h WT/PV/OD profiles, and K-paths generated.\")
# تعداد جاده‌های دارای ظرفیت و زمان آزاد بارگذاری‌شده را چاپ می‌کند.
g7_load_log(\"   ├─ Road capacities and free-flow times loaded: 20 roads (R1-R20).\")
# جمع ظرفیت پایهٔ باد و خورشیدی شبکه را برای کنترل داده‌ها چاپ می‌کند.
g7_load_log(\"   ├─ Total Initial Renewable Capacity (PDN): \$(sum(Der_g1)) kW (WT: \$(sum(wt_capacities)) kW, PV: \$(sum(pv_pdn_capacities)) kW).\")
# طول واقعی پروفایل‌های باد و خورشید و ابعاد تقاضای سفر را چاپ می‌کند؛ این پیام آزمون امکان‌پذیری نیست.
g7_load_log(\"   ├─ 96-hour Profiles verified: WT (len=\$(length(wt_profile))), PV (len=\$(length(pv_profile))), OD (size=\$(size(Df_initial))).\")
# سرآیند گزارش مسیرهای انتخابی بر اساس زمان آزاد را چاپ می‌کند.
g7_load_log(\"   └─ Algorithmic K-Shortest Paths for Sample O-D pairs (sorted by h0_b):\")
# برای گزارش کوتاه، حداکثر سه جفت مبدأ و مقصد نخست را بررسی می‌کند.
for rs in 1:min(3, num_OD_pairs)
    # گره مبدأ و مقصد جفت سفر جاری را برای گزارش مسیرها می‌خواند.
    orig, dest = od_node_pairs[rs]
    # شماره و دو سر جفت مبدأ و مقصد جاری را چاپ می‌کند.
    g7_load_log(\"      * O-D \$rs (T\$orig -> T\$dest):\")
    # همهٔ مسیرهای انتخابی جفت جاری را برای نمایش مشخصات پیمایش می‌کند.
    for k in 1:num_paths
        # فهرست جاده‌های مسیر انتخابی جاری را می‌گیرد.
        p_roads = algorithmic_od_paths[rs][k]
        # مجموع زمان آزاد جاده‌های مسیر را برای گزارش محاسبه می‌کند.
        p_time = sum(h0_b[r] for r in p_roads)
        # جاده‌های مسیر و زمان آزاد آن را با دو رقم اعشار برای بازبینی چاپ می‌کند.
        g7_load_log(\"        Path \$k: Roads \$p_roads | Free-flow time: \$(round(p_time, digits=2)) min\")
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
# حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
end
# جدول خطوط برق را آغاز می‌کند: شین ابتدا، شین انتها، مقاومت و راکتانس اهمی و حد توان فعال.
const PDN_lines_data = [
     # خط برق 1 از شین 1 به 2 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     1   2   0.0922  0.0470  3047.13;
     # خط برق 2 از شین 2 به 3 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     2   3   0.4930  0.2511  2549.40;
     # خط برق 3 از شین 3 به 4 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     3   4   0.3660  0.1864  2164.76;
     # خط برق 4 از شین 4 به 5 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     4   5   0.3811  0.1941  2668.01;
     # خط برق 5 از شین 5 به 6 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     5   6   0.8190  0.7070  2457.81;
     # خط برق 6 از شین 6 به 7 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     6   7   0.1872  0.6188  2300.48;
     # خط برق 7 از شین 7 به 8 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     7   8   0.7114  0.2351  2048.59;
     # خط برق 8 از شین 8 به 9 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     8   9   1.0300  0.7400  2966.33;
     # خط برق 9 از شین 9 به 10 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     9  10   1.0440  0.7400  2688.23;
    # خط برق 10 از شین 10 به 11 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    10  11   0.1966  0.0650  2851.36;
    # خط برق 11 از شین 11 به 12 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    11  12   0.3744  0.1238  2355.47;
    # خط برق 12 از شین 12 به 13 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    12  13   1.4680  1.1550  2705.91;
    # خط برق 13 از شین 13 به 14 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    13  14   0.5416  0.7129  2541.76;
    # خط برق 14 از شین 14 به 15 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    14  15   0.5910  0.5260  2520.55;
    # خط برق 15 از شین 15 به 16 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    15  16   0.7463  0.5450  2286.02;
    # خط برق 16 از شین 16 به 17 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    16  17   1.2890  1.7210  2613.39;
    # خط برق 17 از شین 17 به 18 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    17  18   0.7320  0.5740  2402.82;
     # خط برق 18 از شین 2 به 19 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     2  19   0.1640  0.1565  2596.22;
    # خط برق 19 از شین 19 به 20 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    19  20   1.5042  1.3554  2438.83;
    # خط برق 20 از شین 20 به 21 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    20  21   0.4095  0.4784  2673.81;
    # خط برق 21 از شین 21 به 22 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    21  22   0.7089  0.9373  2590.52;
     # خط برق 22 از شین 3 به 23 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     3  23   0.4512  0.3083  2336.64;
    # خط برق 23 از شین 23 به 24 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    23  24   0.8980  0.7091  2808.84;
    # خط برق 24 از شین 24 به 25 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    24  25   0.8960  0.7011  2707.61;
     # خط برق 25 از شین 6 به 26 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     6  26   0.2030  0.1034  2543.83;
    # خط برق 26 از شین 26 به 27 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    26  27   0.2842  0.1447  2296.86;
    # خط برق 27 از شین 27 به 28 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    27  28   1.0590  0.9337  2302.25;
    # خط برق 28 از شین 28 به 29 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    28  29   0.8042  0.7006  2497.54;
    # خط برق 29 از شین 29 به 30 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    29  30   0.5075  0.2585  2507.18;
    # خط برق 30 از شین 30 به 31 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    30  31   0.9744  0.9630  2243.74;
    # خط برق 31 از شین 31 به 32 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    31  32   0.3105  0.3619  2413.65;
    # خط برق 32 از شین 32 به 33 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    32  33   0.3410  0.5302  2596.15;
    # خط برق 33 از شین 21 به 8 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    21   8   2.0000  2.0000  2379.71;
     # خط برق 34 از شین 9 به 15 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
     9  15   2.0000  2.0000  2427.50;
    # خط برق 35 از شین 12 به 22 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    12  22   2.0000  2.0000  2767.34;
    # خط برق 36 از شین 18 به 33 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    18  33   0.5000  0.5000  2756.41;
    # خط برق 37 از شین 25 به 29 را با مقاومت، راکتانس و حد توان جدول ثبت می‌کند.
    25  29   0.5000  0.5000  2776.44
# تعریف جدول یا بردار PDN_lines_data را تکمیل می‌کند.
]
# ستون شین ابتدایی خطوط را به شماره‌های صحیح تبدیل می‌کند.
const from_bus = Int.(PDN_lines_data[:, 1])
# ستون شین انتهایی خطوط را به شماره‌های صحیح تبدیل می‌کند.
const to_bus   = Int.(PDN_lines_data[:, 2])
# مقاومت هر خط را از ستون سوم جدول بر حسب اهم استخراج می‌کند.
const R_line   = PDN_lines_data[:, 3]
# راکتانس هر خط را از ستون چهارم جدول بر حسب اهم استخراج می‌کند.
const X_line   = PDN_lines_data[:, 4]
# حد جدول خطوط را می‌خواند؛ این مدل آن را برای کران توان فعال به کار می‌برد.
const S_max    = PDN_lines_data[:, 5]
# حد توان فعال پست بالادست را ۴۸۰۰ کیلووات تعیین می‌کند.
const Pb_max      = 4800.0
# حالت پیش‌فرض را بر حفظ حد خط اول جدول قرار می‌دهد.
const LINE1_MODE  = :strict_table11
# بردار کران جریان توان فعال خطوط را با یک کپی از حدود جدول می‌سازد.
const Pf_max      = copy(S_max)
# شرط فعال‌بودن تفسیر جایگزین حد خط اول بر اساس ظرفیت پست را بررسی می‌کند.
if LINE1_MODE == :substation_capacity
    # فقط در حالت جایگزین، کران خط اول را حداقل برابر ظرفیت پست می‌کند.
    Pf_max[1] = max(Pf_max[1], Pb_max)
# شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
end
# حد بالای ولتاژ شین‌ها را بر حسب پریونیت تعریف می‌کند.
const V_max       = 1.05
# حد پایین ولتاژ شین‌ها را بر حسب پریونیت تعریف می‌کند.
const V_min       = 0.93
# ولتاژ مرجع شین پست را بر حسب پریونیت تعریف می‌کند.
const V_slack     = 1.03
# نسبت توان راکتیو به اکتیو منابع تجدیدپذیر را تعیین می‌کند.
const tan_phi     = 0.20
# حد توان ظاهری واحد تجدیدپذیر را بر حسب کیلوولت‌آمپر تعریف می‌کند.
const Sw_max      = 468.00
# کران کمکی اختلاف ولتاژ خطوط رابط را از ولتاژ مرجع می‌گیرد.
const V_bound_dV  = V_slack
# حالت ظرفیت افزایشی را از محیط می‌خواند؛ پیش‌فرض آن پیوسته است.
const SIZING_MODE = :continuous # default is fixed only for structural audit; plan uses --sizing
# تفسیر قید ظرفیت شارژ را صریح می‌کند؛ ابهام معادلهٔ ۳۳ با انتخاب تنظیم رفع قطعی مقاله نمی‌شود.
const CHARGING_CAPACITY_MODE = :printed_eq33 # plan requires explicit --capacity
# فقط دو تفسیر شناخته‌شدهٔ قید ظرفیت شارژ را می‌پذیرد و خطای نام گزینه را رد می‌کند.
CHARGING_CAPACITY_MODE in (:printed_eq33, :installed_capacity) || error(\"Invalid REVCS_CAPACITY\")
# مهلت حل هر مدل را بر حسب ثانیه از متغیر محیطی می‌خواند.
const EVAL_TIME_LIMIT = 600.0 # plan --seconds controls solve budget
# حالت ظرفیت افزایشی را به گزینهٔ پیوسته یا گام ثابت محدود می‌کند.
SIZING_MODE in (:continuous, :discrete_step20) || error(\"Invalid REVCS_SIZING\")
# مثبت‌بودن مهلت حل و سقف تکرار پیکربندی‌شده را کنترل می‌کند.
EVAL_TIME_LIMIT > 0 && rddp_max_iters > 0 || error(\"Time limit and iterations must be positive\")
# آرایهٔ ثبت وضعیت حل، جواب قابل قبول و کران حل‌کننده را ایجاد می‌کند.
const SOLVE_AUDIT = NamedTuple[]

# تابع ذخیرهٔ گزارش وضعیت حل‌ها در فایل جدولی جداشده با تب را تعریف می‌کند.
function save_solve_audit(path=\"revcs_solve_audit.tsv\")
    # فایل گزارش را برای بازنویسی باز می‌کند و بستن خودکار آن را با بلوک do تضمین می‌کند.
    open(path, \"w\") do io
        # نام ستون‌های وضعیت، جواب، کران و شکاف را در سرآیند گزارش ممیزی می‌نویسد.
        println(io, \"context\\ttermination\\tprimal\\tdual\\tincumbent\\tbound\\tgap\")
        # هر سطر ثبت‌شدهٔ ممیزی حل را برای نوشتن در فایل پیمایش می‌کند.
        for r in SOLVE_AUDIT
            # یک سطر گزارش ممیزی حل را با جداکنندهٔ تب در فایل می‌نویسد.
            println(io, join((r.context,r.termination,r.primal,r.dual,r.incumbent,r.bound,r.gap), '\\t'))
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # بلوک پردازش فایل یا ساخت یک‌بارهٔ مقدار حافظه را پایان می‌دهد.
    end
# تعریف تابع save_solve_audit را پایان می‌دهد.
end

# ثبت جواب قابل قبول، کران حل‌کننده و شکاف هر حل را تعریف می‌کند.
function record_solve!(m; context=\"\")
    # جهت کمینه‌سازی یا بیشینه‌سازی تابع هدف را می‌خواند.
    sense = objective_sense(m)
    # جهت مدل را برای تفسیر درست جواب و کران مشخص می‌کند.
    is_min = sense != MOI.MAX_SENSE
    # وجود جواب و وضعیت قابل قبول اولیه را هم‌زمان کنترل می‌کند.
    feasible = has_values(m) && primal_status(m) == MOI.FEASIBLE_POINT
    # مقدار جواب قابل قبول را می‌گیرد و در نبود آن، مقدار بی‌نهایت متناسب با جهت می‌گذارد.
    incumbent = feasible ? objective_value(m) : (is_min ? Inf : -Inf)
    # کران گواه حل‌کننده را می‌خواند؛ در نبود کران، مقدار محافظه‌کارانهٔ بی‌نهایت می‌گذارد.
    bound = try objective_bound(m) catch; is_min ? -Inf : Inf end
    # شکاف را تا زمان دسترسی به دو کران متناهی، نامحدود نگه می‌دارد.
    gap = Inf
    # شرط متناهی‌بودن هم‌زمان جواب قابل قبول و کران حل‌کننده را بررسی می‌کند.
    if isfinite(incumbent) && isfinite(bound)
        # فاصلهٔ جواب قابل قبول و کران حل‌کننده را با جهت صحیح محاسبه می‌کند.
        delta = is_min ? incumbent-bound : bound-incumbent
        # تلرانس مقیاس‌شدهٔ کنترل ناسازگاری کران‌ها را تعیین می‌کند.
        tolerance = 1e-7 * max(1.0,abs(incumbent),abs(bound))
        # ترتیب صحیح کران پایین و بالا را با تلرانس عددی کنترل می‌کند و ناسازگاری را خطا می‌گیرد.
        delta >= -tolerance || error(\"\$context: solver bounds cross: incumbent=\$incumbent, bound=\$bound\")
        # شکاف نسبی غیرمنفی حل ثبت‌شده را محاسبه می‌کند.
        gap = max(0.0,delta)/max(1.0,abs(incumbent))
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # نام حل، وضعیت توقف و وضعیت جواب اولیه را در سطر نام‌دار گزارش ثبت می‌کند.
    row = (; context, termination=termination_status(m), primal=primal_status(m),
            # وضعیت دوگان، جواب قابل قبول، کران و شکاف را به همان سطر گزارش اضافه می‌کند.
            dual=dual_status(m), incumbent, bound, gap)
    # سطر وضعیت این حل را به گزارش ممیزی اضافه می‌کند.
    push!(SOLVE_AUDIT,row)
    # سطر ثبت‌شدهٔ وضعیت حل و دو کران آن را برمی‌گرداند.
    return row
# تعریف تابع record_solve! را پایان می‌دهد.
end

# کنترل صریح وجود جواب بهینه و قابل قبول را تعریف می‌کند.
function require_optimal!(m; context=\"\")
    # پیش از الزام بهینگی، اطلاعات واقعی حل را ثبت می‌کند.
    row = record_solve!(m; context)
    # وجود هم‌زمان وضعیت بهینه و جواب اولیهٔ قابل قبول را برای این رابط الزامی می‌کند.
    row.termination == MOI.OPTIMAL && row.primal == MOI.FEASIBLE_POINT ||
        # با پیام مشخص‌شده توقف می‌کند تا وضعیت فاقد گواه یا ساختار پشتیبانی‌نشده به نتیجهٔ معتبر تبدیل نشود.
        error(\"\$context: no optimal solution: \$row\")
    # سطر ثبت‌شدهٔ وضعیت حل و دو کران آن را برمی‌گرداند.
    return row
# تعریف تابع require_optimal! را پایان می‌دهد.
end
# فرض چرخهٔ باتری را از محیط می‌خواند؛ daily_cyclic فرض اجرایی روزهای نمونه است.
const BATTERY_CYCLE_MODE = :cyclic_free_e0 # legacy symbol; physical builder uses g7cfg().soc_boundary
# SOC اولیهٔ فرض‌شده را می‌خواند؛ پیش‌فرض ۰٫۵ دادهٔ تکمیلی تأییدشدهٔ نویسندگان نیست.
const SOC_INITIAL = 0.5 # structural compatibility only; no implicit plan initial fraction
# حداقل SOC فرض‌شده را می‌خواند؛ پیش‌فرض ۰٫۱ یک فرض مهندسی ثبت‌شده است.
const SOC_MIN = 0.0 # scenario-specific bounds via CLI
# حداکثر SOC فرض‌شده را می‌خواند؛ پیش‌فرض ۰٫۹ یک فرض مهندسی ثبت‌شده است.
const SOC_MAX = 1.0 # scenario-specific bounds via CLI
# ترتیب حدود و مقدار اولیهٔ فرض‌شدهٔ SOC را در بازهٔ صفر تا یک بررسی می‌کند.
0 <= SOC_MIN <= SOC_INITIAL <= SOC_MAX <= 1 || error(\"Invalid SOC assumptions\")
# فقط چرخهٔ روزانه یا اتصال پیوستهٔ ۹۶ ساعتهٔ انرژی باتری را به‌عنوان گزینه می‌پذیرد.
BATTERY_CYCLE_MODE in (:cyclic_free_e0,:continuous_96h) || error(\"Invalid battery cycle mode\")
# حالت قیود تخصیص شارژ را روی روابط استفاده‌شده از مقاله قرار می‌دهد.
const CHARGING_ASSIGNMENT_MODE = :paper_exact
# نسبت توان راکتیو بار به توان اکتیو را در مدل موجود تعریف می‌کند.
const q_fac_load  = 0.30
# نسبت کمکی کران توان راکتیو باتری به توان اکتیو را تعریف می‌کند.
const q_fac_bound = 0.30
# کران توان راکتیو پست را از نسبت بار و حد توان فعال محاسبه می‌کند.
const Qb_max = Pb_max * q_fac_load
# کران توان راکتیو خطوط را به‌صورت عضو به عضو محاسبه می‌کند.
const Qf_max = Pf_max .* q_fac_load
# ضریب تبدیل اهم و کیلووات در معادلهٔ افت ولتاژ را با ولتاژ مبنای ۱۲٫۶۶ کیلوولت می‌سازد.
const base_impedance = NaN # no fixed voltage base; model reads validated CLI
# جدول بار فعال تجمیعی را آغاز می‌کند؛ ۲۴ سطر ساعتی و چهار ستون روز نمونه دارد.
const Load_P_days = [
    # بار فعال کل شبکه در ساعت 1 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2194.56  2395.75  2073.62  2270.24;
    # بار فعال کل شبکه در ساعت 2 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2318.93  2516.61  2239.78  2492.41;
    # بار فعال کل شبکه در ساعت 3 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2179.02  2129.65  2091.06  2038.34;
    # بار فعال کل شبکه در ساعت 4 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2390.44  2165.43  2199.35  2403.66;
    # بار فعال کل شبکه در ساعت 5 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2723.11  2564.21  2650.42  2436.52;
    # بار فعال کل شبکه در ساعت 6 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    3857.93  3596.55  4542.53  3680.43;
    # بار فعال کل شبکه در ساعت 7 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4013.38  3885.87  3662.91  3951.70;
    # بار فعال کل شبکه در ساعت 8 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4168.84  4161.07  3971.99  4962.07;
    # بار فعال کل شبکه در ساعت 9 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4231.02  4260.52  4735.59  4936.19;
    # بار فعال کل شبکه در ساعت 10 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4308.75  4327.83  4294.56  3941.05;
    # بار فعال کل شبکه در ساعت 11 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4595.23  4124.76  4178.37  5037.70;
    # بار فعال کل شبکه در ساعت 12 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4712.93  5124.41  4902.02  4920.10;
    # بار فعال کل شبکه در ساعت 13 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4977.20  4570.90  5217.84  4819.68;
    # بار فعال کل شبکه در ساعت 14 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4782.88  5451.13  5019.09  4628.25;
    # بار فعال کل شبکه در ساعت 15 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4184.38  4594.85  4774.17  4472.51;
    # بار فعال کل شبکه در ساعت 16 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    3857.93  4003.67  3492.06  3442.31;
    # بار فعال کل شبکه در ساعت 17 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4161.06  4013.64  3833.31  4527.05;
    # بار فعال کل شبکه در ساعت 18 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    4122.20  4178.10  3610.70  4421.45;
    # بار فعال کل شبکه در ساعت 19 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    3811.29  3787.13  3884.27  3606.98;
    # بار فعال کل شبکه در ساعت 20 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    3307.62  2915.05  3411.45  3372.55;
    # بار فعال کل شبکه در ساعت 21 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2793.06  3158.99  2579.75  2775.14;
    # بار فعال کل شبکه در ساعت 22 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2629.84  2623.20  2476.20  2701.17;
    # بار فعال کل شبکه در ساعت 23 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2468.16  2312.76  2464.55  2247.30;
    # بار فعال کل شبکه در ساعت 24 را بر حسب کیلووات برای چهار روز نمونه ثبت می‌کند.
    2381.11  2560.89  2391.62  2246.39
# تعریف جدول یا بردار Load_P_days را تکمیل می‌کند.
]
# بار تجمیعی چهار روز را به بردار ۹۶ ساعتی تبدیل می‌کند.
const Total_Load_P_96 = vec(Load_P_days)
# مطابق عنوان جدول ۸ پیوست، بار تجمیعی را یکنواخت بین ۳۳ شین تقسیم می‌کند.
const PD_bus_96 = Total_Load_P_96 ./ num_buses
# بار راکتیو هر شین را با نسبت ثابت بار اکتیو محاسبه می‌کند.
const QD_bus_96 = PD_bus_96 .* q_fac_load
# آماده‌بودن داده‌های شبکهٔ ۳۳ شینه و پروفایل بار را اعلام می‌کند.
g7_load_log(\"✅ [Part 4 Complete] 33-Bus PDN parameters & 96-h load profiles successfully mapped.\")
# تعداد شاخه‌های اصلی و خطوط رابط تعریف‌شده را چاپ می‌کند.
g7_load_log(\"   ├─ Power Lines: 37 paths defined (32 radial + 5 tie-lines).\")
# ولتاژ مرجع و حدود ولتاژ پریونیت را برای کنترل پیکربندی چاپ می‌کند.
g7_load_log(\"   ├─ Base Voltage Params: V_slack=\$(V_slack) pu, V_max=\$(V_max) pu, V_min=\$(V_min) pu.\")
# حدود فعال و راکتیو پست را با واحدهایشان چاپ می‌کند.
g7_load_log(\"   ├─ Substation Limits: Active=\$(Pb_max) kW, Reactive=\$(Qb_max) kVAr.\")
# فرض توزیع یکنواخت بار میان شین‌ها را آشکارا در خروجی اعلام می‌کند.
g7_load_log(\"   └─ Supplement Table 8: 96-h aggregate load divided equally among \$num_buses buses.\")
# هزینهٔ ثابت احداث ایستگاه جدید را تعریف می‌کند.
const q_rvc = 110000.0
# هزینهٔ نگهداری هر ایستگاه فعال در دوره را تعریف می‌کند.
const c_man = 20000.0
# هزینهٔ افزایش هر کیلووات ظرفیت شارژ را تعریف می‌کند.
const q_fc  = 200.0
# هزینهٔ افزایش هر کیلووات‌ساعت ظرفیت انرژی باتری را تعریف می‌کند.
const q_es  = 600.0
# هزینهٔ افزایش هر کیلووات ظرفیت خورشیدی ایستگاه را تعریف می‌کند.
const q_pv  = 1000.0
# ضریب هزینهٔ خرید انرژی از پست بالادست را تعریف می‌کند.
const c_sub = 0.3
# ضریب هزینهٔ محدودسازی تولید تجدیدپذیر را تعریف می‌کند.
const c_cr  = 2.0
# ضریب هزینهٔ عدم‌توازن توان در تابع هدف را تعریف می‌کند.
const c_unb = 10.0
# ضریب هزینهٔ سفر در زمان آزاد جاده را تعریف می‌کند.
const c_fr  = 0.012
# ضریب هزینهٔ ازدحام حمل‌ونقل را تعریف می‌کند.
const c_ja  = 0.04
# نرخ تنزیل بین دوره‌های برنامه‌ریزی را تعیین می‌کند.
const sigma = NaN # mandatory user-selected --sigma in plan
# ظرفیت پایهٔ توان شارژ هر ایستگاه را بر حسب کیلووات تعریف می‌کند.
const Cc_0_kw    = 200.0
# ظرفیت پایهٔ انرژی باتری هر ایستگاه را بر حسب کیلووات‌ساعت تعریف می‌کند.
const Ce_0_kwh   = 40.0
# ظرفیت پایهٔ خورشیدی هر ایستگاه را بر حسب کیلووات تعریف می‌کند.
const Cv_0_kw    = 60.0
# نام کوتاه ظرفیت پایهٔ توان شارژ را تعریف می‌کند.
const Cc_0       = Cc_0_kw
# نام کوتاه ظرفیت پایهٔ انرژی باتری را تعریف می‌کند؛ واحد آن انرژی است.
const Ce_0       = Ce_0_kwh
# نام کوتاه ظرفیت پایهٔ توان خورشیدی ایستگاه را تعریف می‌کند.
const Cv_0       = Cv_0_kw
# حد افزایش ظرفیت شارژ در هر دوره را بر حسب کیلووات تعریف می‌کند.
const Ec_max_kw  = 200.0
# حد افزایش ظرفیت انرژی باتری در هر دوره را بر حسب کیلووات‌ساعت تعریف می‌کند.
const Ee_max_kwh = 40.0
# حد افزایش ظرفیت خورشیدی در هر دوره را بر حسب کیلووات تعریف می‌کند.
const Ev_max_kw  = 60.0
# نام کوتاه حد افزایش توان شارژ را تعریف می‌کند.
const Ec_max     = Ec_max_kw
# نام کوتاه حد افزایش انرژی باتری را تعریف می‌کند.
const Ee_max     = Ee_max_kwh
# نام کوتاه حد افزایش توان خورشیدی را تعریف می‌کند.
const Ev_max     = Ev_max_kw
# یک کران ظرفیت کل شارژ را از ظرفیت پایه و حداکثر افزایش همهٔ دوره‌ها محاسبه می‌کند.
const Cc_max = Cc_0 + num_periods * Ec_max
# کران ظرفیت کل انرژی باتری را برای ساخت شبکهٔ حالت محاسبه می‌کند.
const Ce_max = Ce_0 + num_periods * Ee_max
# کران ظرفیت کل خورشیدی ایستگاه را برای ساخت شبکهٔ حالت محاسبه می‌کند.
const Cv_max = Cv_0 + num_periods * Ev_max
# حد توان فعال شارژ یا تخلیهٔ باتری را ۲۰ کیلووات تعریف می‌کند.
const Pe_max_kw    = 20.0
# نام کوتاه حد توان فعال باتری را تعریف می‌کند.
const Pe_max       = Pe_max_kw
# نسبت حد توان باتری به انرژی پایه را محاسبه می‌کند؛ اینجا برای محدودیت توان متناسب با ظرفیت استفاده می‌شود.
const Pe_ramp_rate = Pe_max_kw / Ce_0_kwh
# بازده شارژ باتری را تعریف می‌کند.
const eta_ch       = 0.95
# بازده تخلیهٔ باتری را تعریف می‌کند.
const eta_dis      = 0.90
# سهم تقاضای سفر متعلق به خودروهای نیازمند شارژ را تعریف می‌کند.
const gamma_12     = 0.24
# نام کوتاه سهم جریان خودروهای نیازمند شارژ را تعریف می‌کند.
const gamma_factor = gamma_12
# ضریب تبدیل نرخ مراجعهٔ خودرو به توان شارژ ایستگاه را تعریف می‌کند.
const delta_p      = NaN # mandatory user-selected --delta-p in plan
# پیش‌بینی رشد تقاضای حمل‌ونقل در سه دوره را ثبت می‌کند.
const theta_fc  = [0.0, 0.40, 0.85]
# دامنهٔ خطای رشد تقاضای حمل‌ونقل را ثبت می‌کند؛ بازهٔ دورهٔ سوم ۱٫۸ تا ۲ برابر پایه می‌شود.
const theta_err = [0.0, 0.10, 0.15]
# پیش‌بینی رشد ظرفیت تجدیدپذیر شبکه را ثبت می‌کند.
const zeta_fc   = [0.0, 0.40, 0.90]
# دامنهٔ خطای رشد ظرفیت تجدیدپذیر را ثبت می‌کند؛ بازهٔ دورهٔ سوم ۱٫۷ تا ۲ برابر پایه است.
const zeta_err  = [0.0, 0.10, 0.10]
# منشأ بازهٔ رشد تجدیدپذیر دورهٔ سوم را متن بخش IV-B ثبت می‌کند؛ تطابق شکل و متن ادعا نمی‌شود.
const dre_period3_range_desc = \"DRE [1.80, 2.00], traffic [1.70, 2.00]; paper IV-B, p.3765\"
# نسبت تغییر خروجی بادی نسبت به پروفایل پایه را تعریف می‌کند.
const xi_wt_err_ratio   = 0.25
# نسبت تغییر خروجی خورشیدی نسبت به پروفایل پایه را تعریف می‌کند.
const zeta_pv_err_ratio = 0.10
# پیام آماده‌بودن پارامترهای اقتصادی و تجهیزات و عدم‌قطعیت را چاپ می‌کند؛ این پیام گواه مستقل تطابق مقاله نیست.
g7_load_log(\"✅ [Part 5 Complete] Economics, REVCS specs, and Uncertainty Set parameters rigorously mapped.\")
# پیام بارگذاری داده و نبود گواه اجرای کامل اوراکل را چاپ می‌کند؛ این پیام قدیمی نتیجهٔ آزمون محاسباتی تازه نیست.
g7_load_log(\"   ├─ Uncertainty data loaded; full-set robust oracle is not certified.\")
# حد ثابت توان باتری و ظرفیت انرژی پایه را چاپ می‌کند؛ مدل علاوه بر نسبت ظرفیت، حد توان ثابت نیز دارد.
g7_load_log(\"   ├─ BESS constraints: Ramp rate limit set exactly at \$Pe_max kW for base \$Ce_0 kWh capacity.\")
# پیام ظرفیت‌ها را چاپ می‌کند؛ واحد درست Ee_max انرژی یعنی کیلووات‌ساعت است، هرچند متن قدیمی پیام kW دارد.
g7_load_log(\"   └─ Expansion bounds: FCS: \$Ec_max kW, BESS: \$Ee_max kWh, PV: \$Ev_max kW (per Table 9).\")

# سازندهٔ مدل فیزیکی یک دوره را تعریف می‌کند؛ این تابع به‌تنهایی بهینه‌سازی را اجرا نمی‌کند.
# Station PV is a separate uncertain process; the physical and symbolic
# builders both must receive its full road-by-hour matrix explicitly.
function require_station_pv_matrix(unc, roads::Int, hours::Int)
    haskey(unc,\"zeta_station_pv\") || error(\"Missing independent zeta_station_pv in scenario\")
    mat=unc[\"zeta_station_pv\"]
    mat isa AbstractMatrix || error(\"zeta_station_pv must be a matrix\")
    size(mat)==(roads,hours) || error(\"zeta_station_pv matrix dimensions mismatch\")
    return mat
end

function build_stage_subproblem(
    # آرگومان «شمارهٔ دورهٔ برنامه‌ریزی» را در امضای تابع مشخص می‌کند.
    t::Int,
    # آرگومان «وضعیت وجود ایستگاه در دورهٔ قبل» را در امضای تابع مشخص می‌کند.
    z_prev,
    # آرگومان «ظرفیت شارژ نصب‌شدهٔ دورهٔ قبل» را در امضای تابع مشخص می‌کند.
    Cc_prev,
    # آرگومان «ظرفیت انرژی باتری دورهٔ قبل» را در امضای تابع مشخص می‌کند.
    Ce_prev,
    # آرگومان «ظرفیت خورشیدی دورهٔ قبل» را در امضای تابع مشخص می‌کند.
    Cv_prev,
    # آرگومان «سناریوی عددی یا نمادین عدم‌قطعیت» را در امضای تابع مشخص می‌کند.
    unc::Dict{String, Any};
    # آرگومان اختیاری مهلت حل را بر حسب ثانیه با مقدار پیکربندی‌شده تعریف می‌کند.
    time_limit_sec::Float64 = EVAL_TIME_LIMIT,
    # ورودی قدیمی نمونه‌های بالایی را می‌پذیرد؛ استفادهٔ غیرخالی آن در این سازنده بعداً صریحاً رد می‌شود.
    upper_samples::Vector = [],
    # مدل مشترک اختیاری را برای افزودن بلوک فیزیکی به مدل نمادین مشخص می‌کند.
    shared_model::Union{Nothing,Model} = nothing,
    # تفسیر ظرفیت شارژ را به‌عنوان آرگومان کلیدی صریح مشخص می‌کند.
    capacity_mode::Symbol = CHARGING_CAPACITY_MODE,
    initial_station_state::AbstractVector{<:Real},
    cfg=g7cfg()
# عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
)
    cfg.source == \"user_selected_not_published\" || error(\"Stage building requires validated explicit Gate7 settings\")
    capacity_mode==cfg.capacity_mode || error(\"Capacity-mode CLI/build mismatch\")
    if t==1 && cfg.initial_state==\"paper_zero\" && capacity_mode==:printed_eq33
        error(\"paper_zero + printed_eq33 is algebraically infeasible by Eq33/34/40\")
    end
    # پیش از ساخت قیود، نام تفسیر ظرفیت شارژ را کنترل می‌کند.
    capacity_mode in (:printed_eq33,:installed_capacity) || error(\"Invalid capacity interpretation\")
    length(initial_station_state)==num_roads || error(\"Initial station-state length mismatch\")
    all(x -> x in (0,1), initial_station_state) || error(\"Initial station state must be binary\")
    if t==1
        for a in A_set
            isapprox(Float64(z_prev[a]),Float64(initial_station_state[a]);atol=1e-10) ||
                error(\"Stage-1 predecessor z does not match selected initial-state branch\")
            isapprox(Float64(Cc_prev[a]),Float64(initial_station_state[a])*Cc_0;atol=1e-8) ||
                error(\"Stage-1 predecessor FCS capacity does not match selected initial-state branch\")
            isapprox(Float64(Ce_prev[a]),Float64(initial_station_state[a])*Ce_0;atol=1e-8) ||
                error(\"Stage-1 predecessor BESS capacity does not match selected initial-state branch\")
            isapprox(Float64(Cv_prev[a]),Float64(initial_station_state[a])*Cv_0;atol=1e-8) ||
                error(\"Stage-1 predecessor PV capacity does not match selected initial-state branch\")
        end
    end
    # برای حل عددی مدل جدید می‌سازد یا برای استخراج نمادین از مدل مشترک ورودی استفاده می‌کند.
    m = shared_model === nothing ? create_highs_model(silent=true, gap=rddp_gap_tol, time_lim=time_limit_sec) : shared_model
    # شرط استفاده از مدل مشترک برای ساخت بلوک نمادین را بررسی می‌کند.
    if shared_model !== nothing
        # نام‌های فعلی ثبت‌شده در مدل مشترک را پیش از ثبت نام‌های بلوک تازه پیمایش می‌کند.
        for key in collect(keys(object_dictionary(m)))
            # نام ثبت‌شدهٔ متغیر یا عبارت را آزاد می‌کند؛ خود متغیرها و قیود مدل حذف نمی‌شوند.
            unregister(m, key)
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # رشد تقاضای حمل‌ونقل سناریوی جاری را می‌خواند.
    theta_t_val = unc[\"theta_t\"]
    # رشد ظرفیت تجدیدپذیر سناریوی جاری را می‌خواند.
    zeta_t_val  = unc[\"zeta_t\"]
    # خروجی بادی سناریو را با پشتیبانی از ماتریس واحدـساعت یا بردار ساعتی می‌خواند.
    get_xi_wt(w, tau)   = (haskey(unc, \"xi_wt\") && unc[\"xi_wt\"] isa AbstractMatrix) ? unc[\"xi_wt\"][w, tau] : (unc[\"xi_wt\"] isa AbstractVector ? unc[\"xi_wt\"][tau] : wt_profile[tau])
    # پروفایل خورشیدی شبکه را از نمایش ماتریسی یا برداری سناریو می‌خواند.
    get_zeta_pv(p, tau) = (haskey(unc, \"zeta_pv\") && unc[\"zeta_pv\"] isa AbstractMatrix) ? unc[\"zeta_pv\"][p, tau] : (unc[\"zeta_pv\"] isa AbstractVector ? unc[\"zeta_pv\"][tau] : pv_profile[tau])
    # Station PV uncertainty is an independently indexed input in Phi_t;
    # never alias it to the network-PV profile when absent or malformed.
    station_pv = require_station_pv_matrix(unc, num_roads, num_tau)
    get_zeta_st(a, tau) = station_pv[a, tau]
    # متغیر دودویی وجود ایستگاه در پایان دوره را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, z[A_set], Bin)
    # متغیر دودویی احداث ایستگاه جدید در این دوره را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, phi_inv[A_set], Bin)
    # متغیر دودویی اجازهٔ توسعهٔ ظرفیت شارژ را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, y_fc[A_set], Bin)
    # متغیر دودویی اجازهٔ توسعهٔ انرژی باتری را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, y_es[A_set], Bin)
    # متغیر دودویی اجازهٔ توسعهٔ خورشیدی ایستگاه را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, y_pv[A_set], Bin)
    # افزایش ظرفیت شارژ بر حسب کیلووات را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, 0 <= Ec[A_set] <= Ec_max)
    # افزایش ظرفیت انرژی باتری بر حسب کیلووات‌ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, 0 <= Ee[A_set] <= Ee_max)
    # افزایش ظرفیت خورشیدی ایستگاه بر حسب کیلووات را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, 0 <= Ev[A_set] <= Ev_max)
    # شرط فعال‌بودن حالت اختیاری افزایش ظرفیت با گام ثابت را بررسی می‌کند.
    if cfg.sizing == :discrete_step20
        # بیشترین تعداد گام‌های صحیح افزایش ظرفیت شارژ را محاسبه می‌کند.
        max_k_fc = Int(round(Ec_max / disc_step_kw))
        # بیشترین تعداد گام‌های صحیح افزایش انرژی باتری را محاسبه می‌کند.
        max_k_es = Int(round(Ee_max / disc_step_kw))
        # بیشترین تعداد گام‌های صحیح افزایش ظرفیت خورشیدی را محاسبه می‌کند.
        max_k_pv = Int(round(Ev_max / disc_step_kw))
        # تعداد صحیح گام‌های توسعهٔ شارژ در حالت گام ثابت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
        @variable(m, 0 <= k_fc[A_set] <= max_k_fc, Int)
        # تعداد صحیح گام‌های توسعهٔ انرژی باتری در حالت گام ثابت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
        @variable(m, 0 <= k_es[A_set] <= max_k_es, Int)
        # تعداد صحیح گام‌های توسعهٔ خورشیدی در حالت گام ثابت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
        @variable(m, 0 <= k_pv[A_set] <= max_k_pv, Int)
        # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
        for a in A_set
            # در حالت اختیاری گام ثابت، افزایش ظرفیت شارژ را مضرب صحیح گام قرار می‌دهد.
            @constraint(m, Ec[a] == disc_step_kw * k_fc[a])
            # در حالت اختیاری، افزایش انرژی باتری را مضرب صحیح گام عددی قرار می‌دهد؛ واحد این مؤلفه کیلووات‌ساعت است.
            @constraint(m, Ee[a] == disc_step_kw * k_es[a])
            # در حالت اختیاری گام ثابت، افزایش ظرفیت خورشیدی را مضرب صحیح گام قرار می‌دهد.
            @constraint(m, Ev[a] == disc_step_kw * k_pv[a])
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # ظرفیت کل نصب‌شدهٔ شارژ بر حسب کیلووات را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Cc[A_set] >= 0)
    # ظرفیت کل نصب‌شدهٔ انرژی باتری بر حسب کیلووات‌ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Ce[A_set] >= 0)
    # ظرفیت کل نصب‌شدهٔ خورشیدی ایستگاه بر حسب کیلووات را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Cv[A_set] >= 0)
    # متغیر کمکی حاصل‌ضرب اجازهٔ توسعه در افزایش ظرفیت شارژ را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, yEc[A_set] >= 0)
    # متغیر کمکی حاصل‌ضرب اجازهٔ توسعه در افزایش انرژی باتری را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, yEe[A_set] >= 0)
    # متغیر کمکی حاصل‌ضرب اجازهٔ توسعه در افزایش ظرفیت خورشیدی را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, yEv[A_set] >= 0)
    # بیت وضعیت شارژ باتری برای هر ایستگاه و ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, v_Ec[A_set, Tau_set], Bin)
    # بیت وضعیت تخلیهٔ باتری برای هر ایستگاه و ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, v_Ed[A_set, Tau_set], Bin)
    # توان فعال مصرف‌شده از تولید بادی بر حسب کیلووات را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pwt[1:length(wt_buses), Tau_set] >= 0)
    # توان راکتیو واحد بادی بر حسب کیلووار را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Qwt[1:length(wt_buses), Tau_set])
    # توان فعال محدودشدهٔ واحد بادی را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pwt_curtail[1:length(wt_buses), Tau_set] >= 0)
    # توان فعال خورشیدی تزریق‌شده در شبکهٔ برق را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Ppv_pdn[1:length(pv_pdn_buses), Tau_set] >= 0)
    # توان راکتیو واحد خورشیدی شبکه را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Qpv_pdn[1:length(pv_pdn_buses), Tau_set])
    # توان فعال محدودشدهٔ خورشیدی شبکه را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Ppv_pdn_curtail[1:length(pv_pdn_buses), Tau_set] >= 0)
    # توان موردنیاز شارژ خودروها در ایستگاه را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pcs[A_set, Tau_set] >= 0)
    # توان خورشیدی استفاده‌شده در ایستگاه را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Rv[A_set, Tau_set] >= 0)
    # توان خورشیدی در دسترس ایستگاه پیش از محدودسازی را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Av[A_set, Tau_set] >= 0)
    # توان خورشیدی محدودشده در ایستگاه را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Rv_curtail[A_set, Tau_set] >= 0)
    # توان فعال شارژ باتری را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pe_Ec[A_set, Tau_set] >= 0)
    # توان فعال تخلیهٔ باتری را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pe_Ed[A_set, Tau_set] >= 0)
    # توان راکتیو متناظر با وضعیت شارژ باتری را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Qe_Ec[A_set, Tau_set] >= 0)
    # توان راکتیو متناظر با وضعیت تخلیهٔ باتری را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Qe_Ed[A_set, Tau_set] >= 0)
    # انرژی ذخیره‌شدهٔ باتری در پایان ساعت بر حسب کیلووات‌ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, E_stored[A_set, Tau_set] >= 0)
    E0 = nothing
    if cfg.soc_boundary==:cyclic_free_e0
        # Named JuMP container: supported @variable syntax, unlike the anonymous
        # comparison expression above. E0 remains the same model variable array.
        @variable(m, G7_DAY_START_E[a in A_set, d in Day_set] >= 0)
        E0 = G7_DAY_START_E
    end
    # توان فعال خالص دریافتی ایستگاه از شبکه، با امکان منفی‌شدن را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pn[A_set, Tau_set])
    # توان فعال دریافتی از پست بالادست را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pb_u[Tau_set] >= 0)
    # توان راکتیو دریافتی از پست بالادست را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Qb_u[Tau_set] >= 0)
    # ولتاژ هر شین و ساعت در محدودهٔ مجاز پریونیت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, V_min <= V_bus[I_set, Tau_set] <= V_max)
    # اختلاف ولتاژ کمکی خطوط رابط را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, dV_line[L_set, Tau_set])
    open_pf_refs=Dict{Tuple{Int,Int},Any}()
    open_qf_refs=Dict{Tuple{Int,Int},Any}()
    closed_dv_refs=Dict{Tuple{Int,Int},Any}()
    # توان فعال جهت‌دار هر خط برق را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Pf[l in L_set, Tau_set])
    # توان راکتیو جهت‌دار هر خط برق را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, Qf[l in L_set, Tau_set])
    # مؤلفهٔ مثبت متغیر کمکی عدم‌توازن توان فعال را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, delta_p_plus[I_set, Tau_set] >= 0)
    # مؤلفهٔ منفی متغیر کمکی عدم‌توازن توان فعال را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, delta_p_minus[I_set, Tau_set] >= 0)
    # مؤلفهٔ مثبت متغیر کمکی عدم‌توازن توان راکتیو را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, delta_q_plus[I_set, Tau_set] >= 0)
    # مؤلفهٔ منفی متغیر کمکی عدم‌توازن توان راکتیو را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, delta_q_minus[I_set, Tau_set] >= 0)
    # جریان خودروهای نیازمند شارژ در هر جاده و ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, x_ch[B_set, Tau_set] >= 0)
    # جریان سایر خودروها در هر جاده و ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, x_un[B_set, Tau_set] >= 0)
    # کل جریان خودرو در هر جاده و ساعت را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, x_total[b in B_set, Tau_set] >= 0)
    # نرخ مراجعهٔ خودرو به ایستگاه شارژ را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, f_pcs[A_set, Tau_set] >= 0)
    # جریان مسیر برای خودروهای نیازمند شارژ را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, f_rs_ch[OD_set, K_set, Tau_set] >= 0)
    # جریان مسیر برای سایر خودروها را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, f_rs_un[OD_set, K_set, Tau_set] >= 0)
    # شرط استفاده از حالت جایگزین چندکالایی کم‌تراکم را بررسی می‌کند.
    if CHARGING_ASSIGNMENT_MODE == :multicommodity_sparse
        # ترکیب‌های معتبر مسیر و ایستگاه را فقط برای حالت جایگزین چندکالایی استخراج می‌کند.
        valid_rsk_a = [(rs, k, a) for rs in OD_set, k in K_set, a in A_set if X_rska[rs, k, a] > 0]
        # جریان اختصاص‌یافته از مسیر به ایستگاه در حالت جایگزین چندکالایی را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
        @variable(m, f_rsk_a[valid_rsk_a, Tau_set] >= 0)
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # متغیر کمکی تأخیر سفر روی جاده را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, h_del[B_set, Tau_set] >= 0)
    # متغیر دوگان قید ظرفیت جاده را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, lambda_b[B_set, Tau_set] >= 0)
    # متغیر دوگان تقاضای سفر خودروهای نیازمند شارژ را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, phi_od_ch[OD_set, Tau_set] >= 0)
    # متغیر دوگان تقاضای سفر سایر خودروها را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, phi_od_un[OD_set, Tau_set] >= 0)
    # متغیر دوگان وقوع جاده برای جریان شارژی را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, mu_b_ch[B_set, Tau_set] >= 0)
    # متغیر دوگان وقوع جاده برای جریان غیرشارژی را با دامنهٔ نشان‌داده‌شده تعریف می‌کند.
    @variable(m, mu_b_un[B_set, Tau_set] >= 0)
    # متغیر نامنفی تقریب هزینهٔ آینده را تعریف می‌کند.
    @variable(m, alpha_cost_to_go >= 0)
    # مرجع قیود اتصال وجود ایستگاه به دورهٔ قبل را ذخیره می‌کند.
    link_z    = Dict{Int, ConstraintRef}()
    # مرجع قیود اتصال ظرفیت شارژ به دورهٔ قبل را ذخیره می‌کند.
    link_Cc   = Dict{Int, ConstraintRef}()
    # مرجع قیود اتصال انرژی باتری به دورهٔ قبل را ذخیره می‌کند.
    link_Ce   = Dict{Int, ConstraintRef}()
    # مرجع قیود اتصال ظرفیت خورشیدی به دورهٔ قبل را ذخیره می‌کند.
    link_Cv   = Dict{Int, ConstraintRef}()
    # وابستگی مستقیم قید ظرفیت شارژ به حالت قبلی را برای جایگزینی بعدی ثبت می‌کند.
    predecessor_capacity_links = Dict{Tuple{Int,Int},ConstraintRef}()
    # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
    for a in A_set
        # افزایش ظرفیت شارژ را فقط هنگام فعال‌بودن تصمیم توسعه مجاز می‌کند.
        @constraint(m, Ec[a] <= Ec_max * y_fc[a])
        # افزایش انرژی باتری را به تصمیم دودویی توسعه و حد دوره محدود می‌کند.
        @constraint(m, Ee[a] <= Ee_max * y_es[a])
        # افزایش ظرفیت خورشیدی را به تصمیم دودویی توسعه و حد دوره محدود می‌کند.
        @constraint(m, Ev[a] <= Ev_max * y_pv[a])
        # بلوک قیود خطی‌سازی حاصل‌ضرب تصمیم توسعه و ظرفیت افزایشی را آغاز می‌کند.
        @constraints(m, begin
            # سه قید خطی دقیق حاصل‌ضرب بیت توسعه در افزایش شارژ را با کران واقعی ظرفیت اعمال می‌کند.
            yEc[a] <= Ec_max * y_fc[a]; yEc[a] <= Ec[a]; yEc[a] >= Ec[a] - Ec_max * (1 - y_fc[a])
            # حاصل‌ضرب بیت توسعه در افزایش انرژی باتری را با کران واقعی همان ظرفیت خطی می‌کند.
            yEe[a] <= Ee_max * y_es[a]; yEe[a] <= Ee[a]; yEe[a] >= Ee[a] - Ee_max * (1 - y_es[a])
            # حاصل‌ضرب بیت توسعه در افزایش خورشیدی را با کران واقعی همان ظرفیت خطی می‌کند.
            yEv[a] <= Ev_max * y_pv[a]; yEv[a] <= Ev[a]; yEv[a] >= Ev[a] - Ev_max * (1 - y_pv[a])
        # بلوک چنددستوری یا مجموعه‌قیود را پایان می‌دهد.
        end)
        # شرط دورهٔ نخست برنامه‌ریزی را بررسی می‌کند.
        if t == 1
            # Eq.37 در دورهٔ اول نسبت به وضعیت اولیهٔ انتخاب‌شده محاسبه می‌شود.
            @constraint(m, phi_inv[a] == z[a] - z_prev[a])
            # Eq.38 ایستگاه اولیه را حذف‌ناپذیر می‌کند؛ در شاخهٔ paper_zero کران اولیه صفر است.
            @constraint(m, z[a] >= z_prev[a])
            # Eq.41 از ظرفیت قبلی + ظرفیت پایهٔ احداث + توسعهٔ مجاز ساخته می‌شود.
            @constraint(m, Cc[a] == Cc_prev[a] + phi_inv[a] * Cc_0 + yEc[a])
            # Eq.42 برای انرژی باتری از همان حالت اولیهٔ صریح استفاده می‌کند.
            @constraint(m, Ce[a] == Ce_prev[a] + phi_inv[a] * Ce_0 + yEe[a])
            # Eq.43 برای PV سقفی از همان حالت اولیهٔ صریح استفاده می‌کند.
            @constraint(m, Cv[a] == Cv_prev[a] + phi_inv[a] * Cv_0 + yEv[a])
        # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
        else
            # وجود ایستگاه در این دوره را با احداث جدید به وضعیت دورهٔ قبل پیوند می‌دهد.
            link_z[a]  = @constraint(m, z[a] - phi_inv[a] == z_prev[a])
            # ظرفیت کل شارژ را به ظرفیت قبلی، ظرفیت پایهٔ احداث و توسعه پیوند می‌دهد.
            link_Cc[a] = @constraint(m, Cc[a] - phi_inv[a] * Cc_0 - yEc[a] == Cc_prev[a])
            # انرژی باتری را به ظرفیت قبلی، ظرفیت پایهٔ احداث و توسعه پیوند می‌دهد.
            link_Ce[a] = @constraint(m, Ce[a] - phi_inv[a] * Ce_0 - yEe[a] == Ce_prev[a])
            # ظرفیت خورشیدی را به ظرفیت قبلی، ظرفیت پایهٔ احداث و توسعه پیوند می‌دهد.
            link_Cv[a] = @constraint(m, Cv[a] - phi_inv[a] * Cv_0 - yEv[a] == Cv_prev[a])
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # هر سه نوع توسعه را فقط برای محل دارای ایستگاه مجاز می‌کند.
        @constraint(m, y_fc[a] <= z[a]); @constraint(m, y_es[a] <= z[a]); @constraint(m, y_pv[a] <= z[a])
        # احداث ایستگاه و توسعهٔ آن در همان دوره را در هر سه مؤلفه هم‌زمان مجاز نمی‌کند.
        @constraint(m, y_fc[a] + phi_inv[a] <= 1); @constraint(m, y_es[a] + phi_inv[a] <= 1); @constraint(m, y_pv[a] + phi_inv[a] <= 1)
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # روی تمام ۹۶ بازهٔ ساعتی حلقه می‌زند.
    for tau in Tau_set
        # روی تمام جفت‌های مبدأ و مقصد حلقه می‌زند.
        for rs in OD_set
            # تقاضای سفر جفت و ساعت جاری را با رشد سناریوی این دوره محاسبه می‌کند.
            Df_rs_t_tau = Df_initial[tau, rs] * (1.0 + theta_t_val)
            # جریان تمام مسیرهای شارژی جفت جاری را برابر سهم شارژی تقاضای سفر می‌کند.
            @constraint(m, sum(f_rs_ch[rs, k, tau] for k in K_set) == gamma_factor * Df_rs_t_tau)
            # جریان سایر خودروها روی مسیرهای جفت جاری را برابر سهم غیرشارژی تقاضا می‌کند.
            @constraint(m, sum(f_rs_un[rs, k, tau] for k in K_set) == (1.0 - gamma_factor) * Df_rs_t_tau)
            # روی تمام مسیرهای انتخابی حلقه می‌زند.
            for k in K_set
                # قید امکان‌پذیری دوگان مسیر را برای گروه خودروهای شارژی اعمال می‌کند.
                @constraint(m, phi_od_ch[rs, tau] - sum(Lambda_rskb[rs, k, b] * mu_b_ch[b, tau] for b in B_set) <= 0)
                # قید امکان‌پذیری دوگان مسیر را برای گروه خودروهای غیرشارژی اعمال می‌کند.
                @constraint(m, phi_od_un[rs, tau] - sum(Lambda_rskb[rs, k, b] * mu_b_un[b, tau] for b in B_set) <= 0)
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # روی همهٔ جاده‌های حمل‌ونقل حلقه می‌زند.
        for b in B_set
            # جریان شارژی هر جاده را از جمع جریان مسیرهای عبوری آن محاسبه می‌کند.
            @constraint(m, x_ch[b, tau] == sum(Lambda_rskb[rs, k, b] * f_rs_ch[rs, k, tau] for rs in OD_set, k in K_set))
            # جریان غیرشارژی هر جاده را از جمع جریان مسیرهای عبوری آن محاسبه می‌کند.
            @constraint(m, x_un[b, tau] == sum(Lambda_rskb[rs, k, b] * f_rs_un[rs, k, tau] for rs in OD_set, k in K_set))
            # کل جریان جاده را برابر مجموع دو گروه خودرو قرار می‌دهد.
            @constraint(m, x_total[b, tau] == x_ch[b, tau] + x_un[b, tau])
            # کل جریان جاده را به ظرفیت ساعتی همان جاده محدود می‌کند.
            @constraint(m, x_total[b, tau] <= phi_b[b])
            # متغیر دوگان ظرفیت را به متغیر تأخیر مورد استفاده در تابع هزینه وصل می‌کند.
            @constraint(m, lambda_b[b, tau] == h_del[b, tau])
            # رابطهٔ دوگان هزینهٔ آزاد و ازدحام را برای گروه شارژی اعمال می‌کند.
            @constraint(m, mu_b_ch[b, tau] - lambda_b[b, tau] == h0_b[b])
            # رابطهٔ دوگان هزینهٔ آزاد و ازدحام را برای گروه غیرشارژی اعمال می‌کند.
            @constraint(m, mu_b_un[b, tau] - lambda_b[b, tau] == h0_b[b])
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # مجموع مراجعه به ایستگاه‌ها را برابر کل تقاضای خودروهای نیازمند شارژ در ساعت جاری می‌کند.
        @constraint(m, sum(f_pcs[a, tau] for a in A_set) == gamma_factor * sum(Df_initial[tau, :]) * (1.0 + theta_t_val))
        # شرط استفاده از روابط تخصیص شارژ حالت مقاله را بررسی می‌کند.
        if CHARGING_ASSIGNMENT_MODE == :paper_exact
            # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
            for a in A_set
                # مراجعهٔ ایستگاه را به جریان شارژی مسیرهایی محدود می‌کند که از محل آن عبور می‌کنند.
                @constraint(m, f_pcs[a, tau] <= sum(X_rska[rs, k, a] * f_rs_ch[rs, k, tau] for rs in OD_set, k in K_set))
                # نرخ مراجعهٔ خودروها را با ضریب مصرف به توان موردنیاز شارژ تبدیل می‌کند.
                @constraint(m, Pcs[a, tau] == cfg.delta_p * f_pcs[a, tau])
                # شرط انتخاب تفسیر چاپی قید ظرفیت شارژ را بررسی می‌کند.
                if capacity_mode == :printed_eq33
                    # تفسیر چاپی معادلهٔ ۳۳ را اعمال و مرجع وابستگی به ظرفیت قبلی را ذخیره می‌کند؛ این تفسیر با ظرفیت نصب‌شده یکسان فرض نمی‌شود.
                    predecessor_capacity_links[(a,tau)] = @constraint(m, Pcs[a, tau] - Ec[a] <= Cc_prev[a])
                # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
                else
                    # در تفسیر جایگزین صریح، توان شارژ را با ظرفیت کل نصب‌شده محدود می‌کند.
                    @constraint(m, Pcs[a, tau] <= Cc[a])
                # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
                end
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
            # تمام ترکیب‌های جفت مبدأ و مقصد و مسیر انتخابی را برای قیود تخصیص شارژ بررسی می‌کند.
            for rs in OD_set, k in K_set
                # جریان شارژی مسیر را به مجموع مراجعهٔ ایستگاه‌های واقع بر همان مسیر محدود می‌کند.
                @constraint(m, f_rs_ch[rs, k, tau] <= sum(X_rska[rs, k, a] * f_pcs[a, tau] for a in A_set))
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
        # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
        else
            # تمام ترکیب‌های جفت مبدأ و مقصد و مسیر انتخابی را برای قیود تخصیص شارژ بررسی می‌کند.
            for rs in OD_set, k in K_set
                # ایستگاه‌های واقع بر مسیر جاری را برای حالت تخصیص چندکالایی استخراج می‌کند.
                valid_stations = [a for a in A_set if X_rska[rs, k, a] > 0]
                # شرط وجود ایستگاه مجاز روی مسیر جاری را بررسی می‌کند.
                if !isempty(valid_stations)
                    # در حالت جایگزین چندکالایی، جریان مسیر را دقیقاً بین ایستگاه‌های مجاز آن تقسیم می‌کند.
                    @constraint(m, f_rs_ch[rs, k, tau] == sum(f_rsk_a[(rs, k, a), tau] for a in valid_stations))
                # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
                else
                    # در حالت چندکالایی، مسیر بدون ایستگاه مجاز را از جریان شارژی تهی می‌کند.
                    @constraint(m, f_rs_ch[rs, k, tau] == 0.0)
                # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
                end
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
            # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
            for a in A_set
                # تمام مسیرهایی را که از ایستگاه جاری عبور می‌کنند استخراج می‌کند.
                valid_paths = [(rs, k) for rs in OD_set, k in K_set if X_rska[rs, k, a] > 0]
                # شرط وجود مسیر عبوری از ایستگاه جاری را بررسی می‌کند.
                if !isempty(valid_paths)
                    # در حالت چندکالایی، مراجعهٔ ایستگاه را از تخصیص تمام مسیرهای عبوری جمع می‌کند.
                    @constraint(m, f_pcs[a, tau] == sum(f_rsk_a[(rs, k, a), tau] for (rs, k) in valid_paths))
                # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
                else
                    # اگر هیچ مسیر مجازی از ایستگاه عبور نکند، مراجعهٔ آن را صفر می‌کند.
                    @constraint(m, f_pcs[a, tau] == 0.0)
                # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
                end
                # نرخ مراجعهٔ خودروها را با ضریب مصرف به توان موردنیاز شارژ تبدیل می‌کند.
                @constraint(m, Pcs[a, tau] == cfg.delta_p * f_pcs[a, tau])
                # شرط انتخاب تفسیر چاپی قید ظرفیت شارژ را بررسی می‌کند.
                if capacity_mode == :printed_eq33
                    # تفسیر چاپی معادلهٔ ۳۳ را اعمال و مرجع وابستگی به ظرفیت قبلی را ذخیره می‌کند؛ این تفسیر با ظرفیت نصب‌شده یکسان فرض نمی‌شود.
                    predecessor_capacity_links[(a,tau)] = @constraint(m, Pcs[a, tau] - Ec[a] <= Cc_prev[a])
                # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
                else
                    # در تفسیر جایگزین صریح، توان شارژ را با ظرفیت کل نصب‌شده محدود می‌کند.
                    @constraint(m, Pcs[a, tau] <= Cc[a])
                # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
                end
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
        for a in A_set
            # تولید خورشیدی در دسترس ایستگاه را از ظرفیت نصب‌شده و پروفایل سناریو محاسبه می‌کند.
            @constraint(m, Av[a, tau] == Cv[a] * get_zeta_st(a, tau))
            # تولید استفاده‌شدهٔ ایستگاه را بیشتر از تولید خورشیدی در دسترس نمی‌گذارد.
            @constraint(m, Rv[a, tau] <= Av[a, tau])
            # تولید خورشیدی در دسترس را به بخش استفاده‌شده و بخش محدودشده تقسیم می‌کند.
            @constraint(m, Rv[a, tau] + Rv_curtail[a, tau] == Av[a, tau])
            # شارژ و تخلیهٔ هم‌زمان را منع می‌کند و در محل فاقد ایستگاه هر دو را صفر می‌کند.
            @constraint(m, v_Ec[a, tau] + v_Ed[a, tau] <= z[a])
            # توان فعال شارژ باتری را به روشن‌بودن حالت شارژ و حد توان ثابت محدود می‌کند.
            # In fixed mode only 20-kW binary limits apply.  In scaled mode
            # two linear constraints represent min(rate*Ce, rate*Ce_max*v).
            if cfg.bess_power_policy==:fixed_20kw
                @constraint(m, Pe_Ec[a,tau] <= Pe_max*v_Ec[a,tau])
                @constraint(m, Pe_Ed[a,tau] <= Pe_max*v_Ed[a,tau])
                @constraint(m, Qe_Ec[a,tau] <= Pe_max*q_fac_bound*v_Ec[a,tau])
                @constraint(m, Qe_Ed[a,tau] <= Pe_max*q_fac_bound*v_Ed[a,tau])
            else
                for (P,Q,vbit) in ((Pe_Ec[a,tau],Qe_Ec[a,tau],v_Ec[a,tau]),
                                   (Pe_Ed[a,tau],Qe_Ed[a,tau],v_Ed[a,tau]))
                    @constraint(m,P <= Pe_ramp_rate*Ce[a])
                    @constraint(m,P <= Pe_ramp_rate*Ce_max*vbit)
                    @constraint(m,Q <= Pe_ramp_rate*q_fac_bound*Ce[a])
                    @constraint(m,Q <= Pe_ramp_rate*q_fac_bound*Ce_max*vbit)
                end
            end
            @constraint(m, Pn[a, tau] == Pcs[a, tau] + Pe_Ec[a, tau] - Pe_Ed[a, tau] - Rv[a, tau])
            # The three SOC policies are mutually exclusive and explicitly scoped.
            @constraint(m,E_stored[a,tau] >= cfg.soc_min*Ce[a])
            @constraint(m,E_stored[a,tau] <= cfg.soc_max*Ce[a])
            charge_delta=Pe_Ec[a,tau]*eta_ch-Pe_Ed[a,tau]/eta_dis
            is_start=(tau-1)%24==0
            is_end=tau%24==0
            if cfg.soc_boundary==:cyclic_free_e0
                d=div(tau-1,24)+1
                if is_start
                    @constraint(m,E0[a,d]>=cfg.soc_min*Ce[a])
                    @constraint(m,E0[a,d]<=cfg.soc_max*Ce[a])
                    @constraint(m,E_stored[a,tau]==E0[a,d]+charge_delta)
                else
                    @constraint(m,E_stored[a,tau]==E_stored[a,tau-1]+charge_delta)
                end
                if is_end
                    @constraint(m,E_stored[a,tau]==E0[a,d])
                end
            elseif cfg.soc_boundary==:fractions
                if is_start
                    @constraint(m,E_stored[a,tau]==cfg.soc_initial*Ce[a]+charge_delta)
                else
                    @constraint(m,E_stored[a,tau]==E_stored[a,tau-1]+charge_delta)
                end
                if is_end
                    @constraint(m,E_stored[a,tau]==cfg.soc_terminal*Ce[a])
                end
            else
                if tau==1
                    @constraint(m,E_stored[a,tau]==cfg.soc_initial*Ce[a]+charge_delta)
                else
                    @constraint(m,E_stored[a,tau]==E_stored[a,tau-1]+charge_delta)
                end
                if tau==num_tau
                    @constraint(m,E_stored[a,tau]==cfg.soc_terminal*Ce[a])
                end
            end
        end
        # تمام واحدهای بادی متصل به شبکهٔ برق را برای قیود تولید پردازش می‌کند.
        for w_idx in 1:length(wt_buses)
            # ضریب خروجی بادی واحد و ساعت جاری را از سناریو می‌گیرد.
            xi_w = get_xi_wt(w_idx, tau)
            # توان بادی استفاده‌شده و محدودشده را برابر تولید در دسترس سناریو قرار می‌دهد.
            @constraint(m, Pwt[w_idx, tau] + Pwt_curtail[w_idx, tau] == (1.0 + zeta_t_val) * wt_capacities[w_idx] * xi_w)
            # توان راکتیو واحد بادی را با نسبت ثابت توان فعال محاسبه می‌کند.
            @constraint(m, Qwt[w_idx, tau] == Pwt[w_idx, tau] * tan_phi)
            # با نسبت راکتیو ثابت، حد توان ظاهری واحد بادی را به قید خطی توان فعال تبدیل می‌کند.
            @constraint(m, Pwt[w_idx, tau] * sqrt(1.0 + tan_phi^2) <= Sw_max)
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # تمام واحدهای خورشیدی شبکهٔ برق را برای قیود تولید پردازش می‌کند.
        for p_idx in 1:length(pv_pdn_buses)
            # ضریب خروجی خورشیدی واحد و ساعت جاری را از سناریو می‌گیرد.
            zeta_p = get_zeta_pv(p_idx, tau)
            # توان خورشیدی شبکهٔ استفاده‌شده و محدودشده را برابر تولید در دسترس سناریو می‌کند.
            @constraint(m, Ppv_pdn[p_idx, tau] + Ppv_pdn_curtail[p_idx, tau] == (1.0 + zeta_t_val) * pv_pdn_capacities[p_idx] * zeta_p)
            # توان راکتیو واحد خورشیدی شبکه را از نسبت ثابت توان فعال می‌سازد.
            @constraint(m, Qpv_pdn[p_idx, tau] == Ppv_pdn[p_idx, tau] * tan_phi)
            # حد توان ظاهری واحد خورشیدی شبکه را با ضریب ثابت به قید خطی تبدیل می‌کند.
            @constraint(m, Ppv_pdn[p_idx, tau] * sqrt(1.0 + tan_phi^2) <= Sw_max)
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # ولتاژ شین مرجع را در ساعت جاری تثبیت می‌کند.
        @constraint(m, V_bus[1, tau] == V_slack)
        # توان فعال پست را به ظرفیت مجاز آن محدود می‌کند.
        @constraint(m, Pb_u[tau] <= Pb_max)
        # توان راکتیو پست را به حد تعریف‌شده محدود می‌کند.
        @constraint(m, Qb_u[tau] <= Qb_max)
        # روی همهٔ شین‌های برق حلقه می‌زند.
        for i in I_set
            # تزریق فعال پست را فقط در شین ۱ وارد موازنه می‌کند.
            p_sub = (i == 1) ? Pb_u[tau] : 0.0
            # تزریق راکتیو پست را فقط در شین ۱ وارد موازنه می‌کند.
            q_sub = (i == 1) ? Qb_u[tau] : 0.0
            # مجموع بار فعال ایستگاه‌های متصل به شین جاری را از صفر آغاز می‌کند.
            p_station = 0.0
            # مجموع بار راکتیو ایستگاه‌های متصل به شین جاری را از صفر آغاز می‌کند.
            q_station = 0.0
            # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
            for a in A_set
                # شرط اتصال ایستگاه جاری به شین برق مورد بررسی را بررسی می‌کند.
                if candidate_road_to_bus[a] == i
                    # توان فعال خالص ایستگاه متصل را به بار شین اضافه می‌کند.
                    p_station += Pn[a, tau]
                    # اثر خالص راکتیو شارژ و تخلیهٔ باتری ایستگاه را در شین جمع می‌کند.
                    q_station += (Qe_Ec[a, tau] - Qe_Ed[a, tau])
                # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
                end
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
            # اندیس واحد بادی متصل به شین جاری را، در صورت وجود، پیدا می‌کند.
            wt_idx = findfirst(x -> x == i, wt_buses)
            # تزریق فعال بادی شین را می‌گیرد یا برای شین فاقد باد صفر می‌گذارد.
            p_wind = (wt_idx !== nothing) ? Pwt[wt_idx, tau] : 0.0
            # تزریق راکتیو بادی شین را می‌گیرد یا صفر می‌گذارد.
            q_wind = (wt_idx !== nothing) ? Qwt[wt_idx, tau] : 0.0
            # اندیس واحد خورشیدی شبکه در شین جاری را پیدا می‌کند.
            pv_idx    = findfirst(x -> x == i, pv_pdn_buses)
            # تزریق فعال خورشیدی شبکه در شین جاری را می‌گیرد یا صفر می‌گذارد.
            p_pv_grid = (pv_idx !== nothing) ? Ppv_pdn[pv_idx, tau] : 0.0
            # تزریق راکتیو خورشیدی شبکه در شین جاری را می‌گیرد یا صفر می‌گذارد.
            q_pv_grid = (pv_idx !== nothing) ? Qpv_pdn[pv_idx, tau] : 0.0
            # سمت تزریق و ورود توان فعال همراه متغیر عدم‌توازن را در موازنهٔ شین می‌نویسد.
            @constraint(m, p_sub + sum(Pf[l, tau] for l in findall(x -> x == i, to_bus)) + p_wind + p_pv_grid + delta_p_plus[i, tau] - delta_p_minus[i, tau] ==
                # سمت خروج توان فعال، بار پایه و تقاضای خالص ایستگاه را در همان موازنه تکمیل می‌کند.
                sum(Pf[l, tau] for l in findall(x -> x == i, from_bus)) + PD_bus_96[tau] + p_station)
            # سمت تزریق و ورود توان راکتیو را در موازنهٔ شین می‌نویسد.
            @constraint(m, q_sub + sum(Qf[l, tau] for l in findall(x -> x == i, to_bus)) + q_wind + q_pv_grid ==
                # خروج توان راکتیو، عدم‌توازن، بار پایه و اثر باتری ایستگاه را در موازنه تکمیل می‌کند.
                sum(Qf[l, tau] for l in findall(x -> x == i, from_bus)) + delta_q_plus[i, tau] - delta_q_minus[i, tau] + QD_bus_96[tau] + q_station)
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # روی همهٔ خطوط برق حلقه می‌زند.
        for l in L_set
            if cfg.topology.status[l]==1
                closed_dv_refs[(l,tau)]=@constraint(m,dV_line[l,tau]==0.0)
                @constraint(m,V_bus[from_bus[l],tau] == V_bus[to_bus[l],tau] +
                    (R_line[l]*Pf[l,tau]+X_line[l]*Qf[l,tau])/
                    (1000.0*cfg.voltage_base_kv^2*V_slack))
            else
                # Open tie: zero active/reactive current. dV simply absorbs
                # the permissible voltage difference, never transmits power.
                open_pf_refs[(l,tau)]=@constraint(m,Pf[l,tau]==0.0)
                open_qf_refs[(l,tau)]=@constraint(m,Qf[l,tau]==0.0)
                @constraint(m,dV_line[l,tau]==V_bus[from_bus[l],tau]-V_bus[to_bus[l],tau])
            end
            @constraint(m,-V_bound_dV<=dV_line[l,tau]<=V_bound_dV)
            @constraint(m,-Pf_max[l]<=Pf[l,tau]<=Pf_max[l])
            @constraint(m,-Qf_max[l]<=Qf[l,tau]<=Qf_max[l])
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # قید برابری هزینهٔ اولیه و دوگان تخصیص ترافیک را به‌صورت چندخطی آغاز می‌کند.
    @constraint(m,
        # سهم تقاضای گروه شارژی در هدف دوگان تخصیص ترافیک را جمع می‌کند.
        sum(gamma_factor * phi_od_ch[rs, tau] * (Df_initial[tau, rs] * (1.0 + theta_t_val)) +
            # سهم گروه غیرشارژی را اضافه و مجموع هدف دوگان را برابر سمت اولیه قرار می‌دهد.
            (1.0 - gamma_factor) * phi_od_un[rs, tau] * (Df_initial[tau, rs] * (1.0 + theta_t_val)) for tau in Tau_set, rs in OD_set) ==
        # سمت هزینهٔ مسیرها و سهم ظرفیت در برابری اولیه و دوگان تخصیص ترافیک را محاسبه می‌کند.
        sum(h0_b[b] * (x_ch[b, tau] + x_un[b, tau]) + phi_b[b] * lambda_b[b, tau] for tau in Tau_set, b in B_set)
    # عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
    )
    # عبارت کمکی تولید در دسترس همهٔ منابع تجدیدپذیر شبکه را آغاز می‌کند.
    @expression(m, Aw[g in 1:length(dre_buses), tau in Tau_set],
        # بسته به بادی یا خورشیدی بودن منبع، شاخهٔ متناظر محاسبه را انتخاب می‌کند.
        (g <= length(wt_buses)) ?
            # برای منبع بادی، رشد ظرفیت و پروفایل بادی سناریو را در ظرفیت پایه ضرب می‌کند.
            (1.0 + zeta_t_val) * wt_capacities[g] * get_xi_wt(g, tau) :
            # برای منبع خورشیدی شبکه، رشد ظرفیت و پروفایل خورشید را در ظرفیت پایه ضرب می‌کند.
            (1.0 + zeta_t_val) * pv_pdn_capacities[g - length(wt_buses)] * get_zeta_pv(g - length(wt_buses), tau)
    # عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
    )
    # ضریب تنزیل هزینه‌های جاری دوره را محاسبه می‌کند.
    discount_factor = 1.0 / (1.0 + cfg.sigma)^(t-1)
    # هزینهٔ احداث و توسعهٔ شارژ، باتری و خورشیدی همهٔ ایستگاه‌ها را جمع می‌کند.
    Inv_Cost = @expression(m, sum(q_rvc * phi_inv[a] + q_fc * yEc[a] + q_es * yEe[a] + q_pv * yEv[a] for a in A_set))
    # عبارت هزینهٔ بهره‌برداری شبکهٔ برق را آغاز می‌کند.
    Ope_Cost_PDN = @expression(m,
        # هزینهٔ خرید توان پست را روی بازه‌های یک‌ساعته جمع می‌کند.
        sum(c_sub * Pb_u[tau] for tau in Tau_set) +
        # هزینهٔ محدودسازی باد، خورشیدی شبکه و خورشیدی ایستگاه‌ها را جمع می‌کند.
        c_cr * (sum(Pwt_curtail[:, Tau_set]) + sum(Ppv_pdn_curtail[:, Tau_set]) + sum(Rv_curtail[:, Tau_set])) +
        # هزینهٔ قدرمطلق عدم‌توازن‌های فعال و راکتیو را با متغیرهای نامنفی جمع می‌کند.
        c_unb * (sum(delta_p_plus) + sum(delta_p_minus) + sum(delta_q_minus) + sum(delta_q_plus))
    # عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
    )
    # عبارت هزینهٔ بهره‌برداری شبکهٔ حمل‌ونقل را آغاز می‌کند.
    Ope_Cost_UTN = @expression(m,
        # هزینهٔ زمان سفر آزاد را برای جریان هر دو گروه خودرو جمع می‌کند.
        c_fr * sum(h0_b[b] * (x_ch[b, tau] + x_un[b, tau]) for b in B_set, tau in Tau_set) +
        # هزینهٔ ازدحام را با ظرفیت جاده و متغیر تأخیر جمع می‌کند.
        c_ja * sum(phi_b[b] * h_del[b, tau] for b in B_set, tau in Tau_set)
    # عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
    )
    # هزینهٔ نگهداری ایستگاه‌ها و هزینه‌های بهره‌برداری برق و حمل‌ونقل را جمع می‌کند.
    Ope_Cost_Total = @expression(m, sum(c_man * z[a] for a in A_set) + cfg.ope_scale*(Ope_Cost_PDN + Ope_Cost_UTN))
    # شرط ارسال نمونه به رابط قدیمی بدون گواه تقریب بالایی را بررسی می‌کند.
    if !isempty(upper_samples)
        # استفاده از تقریب بالایی قدیمی بدون گواه هزینه و کدگذاری حالت را صریحاً رد می‌کند.
        error(\"Uncertified hull disabled: Eq. (61) needs certified robust sample values and binary state encoding\")
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # هزینهٔ تنزیل‌شدهٔ جاری به‌اضافهٔ تقریب هزینهٔ آینده را کمینه می‌کند.
    @objective(m, Min, discount_factor * (Inv_Cost + Ope_Cost_Total) + alpha_cost_to_go)
    # فرهنگ خروجی متغیرها، قیود اتصال و عبارت‌های هزینه را ایجاد می‌کند.
    vars = Dict(
        \"theta_t\" => theta_t_val, \"zeta_t\" => zeta_t_val,
        \"xi_wt_profile\" => [get_xi_wt(w,tau) for w in eachindex(wt_buses),tau in Tau_set],
        \"zeta_pv_profile\" => [get_zeta_pv(w,tau) for w in eachindex(pv_pdn_buses),tau in Tau_set],
        \"zeta_station_pv_profile\" => [get_zeta_st(a,tau) for a in A_set,tau in Tau_set],
        # ورودی‌های «متغیر دودویی وجود ایستگاه در پایان دوره، متغیر دودویی احداث ایستگاه جدید در این دوره، متغیر دودویی اجازهٔ توسعهٔ ظرفیت شارژ، متغیر دودویی اجازهٔ توسعهٔ انرژی باتری، متغیر دودویی اجازهٔ توسعهٔ خورشیدی ایستگاه» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"z\" => z, \"phi_inv\" => phi_inv, \"y_fc\" => y_fc, \"y_es\" => y_es, \"y_pv\" => y_pv,
        # ورودی‌های «افزایش ظرفیت شارژ بر حسب کیلووات، افزایش ظرفیت انرژی باتری بر حسب کیلووات‌ساعت، افزایش ظرفیت خورشیدی ایستگاه بر حسب کیلووات» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Ec\" => Ec, \"Ee\" => Ee, \"Ev\" => Ev,
        \"yEc\" => yEc, \"yEe\" => yEe, \"yEv\" => yEv,
        # ورودی‌های «ظرفیت کل نصب‌شدهٔ شارژ بر حسب کیلووات، ظرفیت کل نصب‌شدهٔ انرژی باتری بر حسب کیلووات‌ساعت، ظرفیت کل نصب‌شدهٔ خورشیدی ایستگاه بر حسب کیلووات» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Cc\" => Cc, \"Ce\" => Ce, \"Cv\" => Cv,
        # ورودی‌های «وضعیت وجود ایستگاه در دورهٔ قبل، ظرفیت شارژ نصب‌شدهٔ دورهٔ قبل، ظرفیت انرژی باتری دورهٔ قبل، ظرفیت خورشیدی دورهٔ قبل» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"z_prev\" => z_prev, \"Cc_prev\" => Cc_prev, \"Ce_prev\" => Ce_prev, \"Cv_prev\" => Cv_prev,
        # ورودی‌های «link_z، link_Cc، link_Ce، link_Cv» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"link_z\" => link_z, \"link_Cc\" => link_Cc, \"link_Ce\" => link_Ce, \"link_Cv\" => link_Cv,
        # ورودی‌های «predecessor_capacity_links» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"predecessor_capacity_links\" => predecessor_capacity_links,
        # ورودی‌های «متغیر نامنفی تقریب هزینهٔ آینده» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"alpha_cost_to_go\" => alpha_cost_to_go,
        # ورودی‌های «Inv_Cost، Ope_Cost_Total» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Inv_Cost\" => Inv_Cost, \"Ope_Cost_Total\" => Ope_Cost_Total,
        # ورودی‌های «Ope_Cost_PDN، Ope_Cost_UTN» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Ope_Cost_PDN\" => Ope_Cost_PDN, \"Ope_Cost_UTN\" => Ope_Cost_UTN,
        # ورودی‌های «جریان خودروهای نیازمند شارژ در هر جاده و ساعت، جریان سایر خودروها در هر جاده و ساعت، کل جریان خودرو در هر جاده و ساعت» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"x_ch\" => x_ch, \"x_un\" => x_un, \"x_total\" => x_total,
        # ورودی‌های «نرخ مراجعهٔ خودرو به ایستگاه شارژ، توان موردنیاز شارژ خودروها در ایستگاه، توان خورشیدی استفاده‌شده در ایستگاه، توان خورشیدی در دسترس ایستگاه پیش از محدودسازی، توان خورشیدی محدودشده در ایستگاه، توان فعال خالص دریافتی ایستگاه از شبکه، با امکان منفی‌شدن» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"f_pcs\" => f_pcs, \"f_rs_ch\"=>f_rs_ch, \"f_rs_un\"=>f_rs_un, \"Pcs\" => Pcs, \"Rv\" => Rv, \"Av\" => Av, \"Rv_curtail\" => Rv_curtail, \"Pn\" => Pn,
        # ورودی‌های «توان فعال تخلیهٔ باتری، توان فعال شارژ باتری، توان راکتیو متناظر با وضعیت تخلیهٔ باتری، توان راکتیو متناظر با وضعیت شارژ باتری» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Pe_Ed\" => Pe_Ed, \"Pe_Ec\" => Pe_Ec, \"Qe_Ed\" => Qe_Ed, \"Qe_Ec\" => Qe_Ec,
        # ورودی‌های «بیت وضعیت شارژ باتری برای هر ایستگاه و ساعت، بیت وضعیت تخلیهٔ باتری برای هر ایستگاه و ساعت، انرژی ذخیره‌شدهٔ باتری در پایان ساعت بر حسب کیلووات‌ساعت» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"v_Ec\" => v_Ec, \"v_Ed\" => v_Ed, \"E_stored\" => E_stored, \"E0\" => E0,
        # ورودی‌های «توان فعال دریافتی از پست بالادست، توان راکتیو دریافتی از پست بالادست، توان فعال مصرف‌شده از تولید بادی بر حسب کیلووات، توان راکتیو واحد بادی بر حسب کیلووار، توان فعال خورشیدی تزریق‌شده در شبکهٔ برق، توان راکتیو واحد خورشیدی شبکه» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Pb_u\" => Pb_u, \"Qb_u\" => Qb_u, \"Pwt\" => Pwt, \"Qwt\" => Qwt, \"Ppv_pdn\" => Ppv_pdn, \"Qpv_pdn\" => Qpv_pdn,
        # ورودی‌های «Aw، ولتاژ هر شین و ساعت در محدودهٔ مجاز پریونیت، توان فعال جهت‌دار هر خط برق، توان راکتیو جهت‌دار هر خط برق، اختلاف ولتاژ کمکی خطوط رابط» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Aw\" => Aw, \"V_bus\" => V_bus, \"Pf\" => Pf, \"Qf\" => Qf, \"dV_line\" => dV_line,
        \"open_pf_refs\"=>open_pf_refs,\"open_qf_refs\"=>open_qf_refs,\"closed_dv_refs\"=>closed_dv_refs,
        # ورودی‌های «متغیر دوگان قید ظرفیت جاده، متغیر کمکی تأخیر سفر روی جاده» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"lambda_b\" => lambda_b, \"h_del\" => h_del,
        # ورودی‌های «متغیر دوگان تقاضای سفر خودروهای نیازمند شارژ، متغیر دوگان تقاضای سفر سایر خودروها، متغیر دوگان وقوع جاده برای جریان شارژی، متغیر دوگان وقوع جاده برای جریان غیرشارژی» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"phi_od_ch\" => phi_od_ch, \"phi_od_un\" => phi_od_un, \"mu_b_ch\" => mu_b_ch, \"mu_b_un\" => mu_b_un,
        # ورودی‌های «مؤلفهٔ مثبت متغیر کمکی عدم‌توازن توان فعال، مؤلفهٔ منفی متغیر کمکی عدم‌توازن توان فعال، مؤلفهٔ مثبت متغیر کمکی عدم‌توازن توان راکتیو، مؤلفهٔ منفی متغیر کمکی عدم‌توازن توان راکتیو» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"delta_p_plus\" => delta_p_plus, \"delta_p_minus\" => delta_p_minus, \"delta_q_plus\" => delta_q_plus, \"delta_q_minus\" => delta_q_minus,
        # ورودی‌های «توان فعال محدودشدهٔ واحد بادی، توان فعال محدودشدهٔ خورشیدی شبکه» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"Pwt_curtail\" => Pwt_curtail, \"Ppv_pdn_curtail\" => Ppv_pdn_curtail
    # عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
    )
    # مدل حل‌نشده و فرهنگ ارجاع متغیرها، قیود اتصال و هزینه‌ها را برمی‌گرداند.
    return m, vars
# تعریف تابع build_stage_subproblem را پایان می‌دهد.
end

# وضعیت فیزیکی وجود ایستگاه و ظرفیت‌های نصب‌شدهٔ پایان دوره را در یک ساختار نگه می‌دارد.
mutable struct StageState
    # فیلد z را برای بردار وجود ایستگاه برای تمام جاده‌ها با نوع مشخص‌شده نگه می‌دارد.
    z::Vector{Float64}
    # فیلد Cc را برای بردار ظرفیت توان شارژ ایستگاه‌ها با نوع مشخص‌شده نگه می‌دارد.
    Cc::Vector{Float64}
    # فیلد Ce را برای بردار ظرفیت انرژی باتری ایستگاه‌ها با نوع مشخص‌شده نگه می‌دارد.
    Ce::Vector{Float64}
    # فیلد Cv را برای بردار ظرفیت خورشیدی ایستگاه‌ها با نوع مشخص‌شده نگه می‌دارد.
    Cv::Vector{Float64}
# تعریف ساختار StageState را پایان می‌دهد.
end

# نگاشت بیت‌های عدم‌قطعیت به مقادیر رشد و پروفایل‌های فیزیکی را تعریف می‌کند.
function create_uncertainty_scenario(
    # آرگومان «نام سناریوی عدم‌قطعیت» را در امضای تابع مشخص می‌کند.
    name::String,
    # آرگومان «شمارهٔ دورهٔ برنامه‌ریزی» را در امضای تابع مشخص می‌کند.
    t::Int,
    # آرگومان «بیت انحراف مثبت رشد تقاضای سفر» را در امضای تابع مشخص می‌کند.
    omega_u_plus::Float64,
    # آرگومان «بیت انحراف منفی رشد تقاضای سفر» را در امضای تابع مشخص می‌کند.
    omega_u_minus::Float64,
    # آرگومان «بیت انحراف مثبت رشد ظرفیت تجدیدپذیر» را در امضای تابع مشخص می‌کند.
    omega_p_plus::Float64,
    # آرگومان «بیت انحراف منفی رشد ظرفیت تجدیدپذیر» را در امضای تابع مشخص می‌کند.
    omega_p_minus::Float64,
    # آرگومان «ماتریس بیت انحراف مثبت خروجی باد» را در امضای تابع مشخص می‌کند.
    beta_wt_plus::Matrix{Float64},
    # آرگومان «ماتریس بیت انحراف منفی خروجی باد» را در امضای تابع مشخص می‌کند.
    beta_wt_minus::Matrix{Float64},
    # آرگومان «ماتریس بیت انحراف مثبت خورشیدی شبکه» را در امضای تابع مشخص می‌کند.
    beta_pv_plus::Matrix{Float64},
    # آرگومان «ماتریس بیت انحراف منفی خورشیدی شبکه» را در امضای تابع مشخص می‌کند.
    beta_pv_minus::Matrix{Float64},
    # آرگومان «ماتریس بیت انحراف مثبت خورشیدی ایستگاه‌ها» را در امضای تابع مشخص می‌کند.
    psi_plus::Matrix{Float64},
    # آرگومان «ماتریس بیت انحراف منفی خورشیدی ایستگاه‌ها» را در امضای تابع مشخص می‌کند.
    psi_minus::Matrix{Float64}
# عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
)
    # رشد تقاضای سفر را از پیش‌بینی و بیت‌های انحراف مثبت و منفی می‌سازد.
    theta_val = theta_fc[t] + omega_u_plus * theta_err[t] - omega_u_minus * theta_err[t]
    # رشد ظرفیت تجدیدپذیر را از پیش‌بینی و بیت‌های انحراف مثبت و منفی می‌سازد.
    zeta_val  = zeta_fc[t] + omega_p_plus * zeta_err[t] - omega_p_minus * zeta_err[t]
    # ماتریس خروجی بادی واحدها و ساعت‌ها را برای ساخت سناریو ایجاد می‌کند.
    xi_wt_mat = zeros(num_wt, num_tau)
    # خروجی سناریوی هر واحد بادی را در هر ساعت محاسبه می‌کند.
    for w in 1:num_wt, tau in Tau_set
        # خروجی بادی واحد و ساعت جاری را از پروفایل پایه و انحراف دودویی مثبت و منفی محاسبه می‌کند.
        xi_wt_mat[w, tau] = wt_profile[tau] * (1.0 + xi_wt_err_ratio * beta_wt_plus[w, tau] - xi_wt_err_ratio * beta_wt_minus[w, tau])
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # ماتریس خروجی خورشیدی واحدهای شبکه و ساعت‌ها را ایجاد می‌کند.
    zeta_pv_mat = zeros(num_pv_pdn, num_tau)
    # خروجی سناریوی هر واحد خورشیدی شبکه را در هر ساعت محاسبه می‌کند.
    for p in 1:num_pv_pdn, tau in Tau_set
        # خروجی خورشیدی شبکه را با انحراف‌های دودویی مستقل هر واحد و ساعت می‌سازد.
        zeta_pv_mat[p, tau] = pv_profile[tau] * (1.0 + zeta_pv_err_ratio * beta_pv_plus[p, tau] - zeta_pv_err_ratio * beta_pv_minus[p, tau])
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # ماتریس خورشیدی محل تمام ایستگاه‌ها و ساعت‌ها را ایجاد می‌کند.
    zeta_st_mat = zeros(num_roads, num_tau)
    # خروجی خورشیدی هر محل ایستگاه را در تمام ساعت‌ها محاسبه می‌کند.
    for a in 1:num_roads, tau in Tau_set
        # خروجی خورشیدی محل ایستگاه را از پروفایل پایه و بیت‌های مستقل همان محل و ساعت محاسبه می‌کند.
        zeta_st_mat[a, tau] = pv_profile[tau] * (1.0 + zeta_pv_err_ratio * psi_plus[a, tau] - zeta_pv_err_ratio * psi_minus[a, tau])
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # برای ورودی‌های دودویی، حاصل‌ضرب دو بیت مثبت را با عمل AND معادل محاسبه می‌کند.
    varpi_wt_plus = [min(omega_p_plus, beta_wt_plus[w, tau]) for w in 1:num_wt, tau in Tau_set]
    # سناریوی فیزیکی و فرادادهٔ بیت‌های سازندهٔ آن را در فرهنگ داده برمی‌گرداند.
    return Dict{String, Any}(
        # ورودی‌های «نام سناریوی عدم‌قطعیت» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"name\" => name,
        # ورودی‌های «theta_t» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"theta_t\" => theta_val,
        # ورودی‌های «zeta_t» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"zeta_t\"  => zeta_val,
        # ورودی‌های «xi_wt» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"xi_wt\"   => xi_wt_mat,
        # ورودی‌های «zeta_pv» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"zeta_pv\" => zeta_pv_mat,
        # ورودی‌های «zeta_station_pv» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"zeta_station_pv\" => zeta_st_mat,
        # ورودی‌های «بیت انحراف مثبت رشد تقاضای سفر، بیت انحراف منفی رشد تقاضای سفر» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"omega_u_plus\" => omega_u_plus, \"omega_u_minus\" => omega_u_minus,
        # ورودی‌های «بیت انحراف مثبت رشد ظرفیت تجدیدپذیر، بیت انحراف منفی رشد ظرفیت تجدیدپذیر» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"omega_p_plus\" => omega_p_plus, \"omega_p_minus\" => omega_p_minus,
        # ورودی‌های «ماتریس بیت انحراف مثبت خروجی باد، ماتریس بیت انحراف منفی خروجی باد» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"beta_wt_plus\" => beta_wt_plus, \"beta_wt_minus\" => beta_wt_minus,
        # ورودی‌های «ماتریس بیت انحراف مثبت خورشیدی شبکه، ماتریس بیت انحراف منفی خورشیدی شبکه» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"beta_pv_plus\" => beta_pv_plus, \"beta_pv_minus\" => beta_pv_minus,
        # ورودی‌های «ماتریس بیت انحراف مثبت خورشیدی ایستگاه‌ها، ماتریس بیت انحراف منفی خورشیدی ایستگاه‌ها» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"psi_plus\" => psi_plus, \"psi_minus\" => psi_minus,
        # ورودی‌های «varpi_wt_plus» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"varpi_wt_plus\" => varpi_wt_plus
    # عبارت چندخطی، فهرست آرگومان‌ها یا فرهنگ دادهٔ در حال ساخت را تکمیل می‌کند.
    )
# تعریف تابع create_uncertainty_scenario را پایان می‌دهد.
end

# کنترل ابعاد، بازه و مقادیر سه‌حالتهٔ سناریوی عدم‌قطعیت را تعریف می‌کند.
function validate_scenario(t, s; atol=1e-8)
    # رشد تقاضا و رشد تجدیدپذیر را همراه پیش‌بینی و دامنهٔ خطای هرکدام اعتبارسنجی می‌کند.
    for (key, forecast, err) in ((\"theta_t\",theta_fc[t],theta_err[t]), (\"zeta_t\",zeta_fc[t],zeta_err[t]))
        # عضویت مقدار یا نمونه در دامنهٔ تعریف‌شده را با تلرانس مشخص کنترل می‌کند.
        isfinite(s[key]) && abs(s[key]-forecast) <= err+atol || error(\"\$key outside Phi_\$t\")
        # شرط غیرصفر بودن دامنهٔ خطای رشد با تلرانس عددی را بررسی می‌کند.
        if err > atol
            # انحراف رشد از پیش‌بینی را بر دامنهٔ خطا تقسیم می‌کند تا مقدار سه‌حالتهٔ آن کنترل شود.
            u = (s[key]-forecast)/err
            # با کنترل صحیح‌بودن انحراف نرمال‌شده، آن را به سه مقدار منفی یک، صفر یا مثبت یک حاصل از اختلاف دو بیت محدود می‌کند.
            abs(u-round(u)) <= atol || error(\"\$key violates binary Eq. (52)\")
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # پروفایل‌های باد و خورشید را با ابعاد، مقدار پایه و نسبت خطای مربوط به هر نوع کنترل می‌کند.
    for (key, rows, profile, ratio) in ((\"xi_wt\",num_wt,wt_profile,xi_wt_err_ratio),
            # پروفایل خورشیدی شبکه، تعداد واحدها و نسبت خطای آن را به فهرست اعتبارسنجی اضافه می‌کند.
            (\"zeta_pv\",num_pv_pdn,pv_profile,zeta_pv_err_ratio),
            # پروفایل خورشیدی ایستگاه‌ها و ابعاد و نسبت خطای آن را به فهرست اعتبارسنجی اضافه می‌کند.
            (\"zeta_station_pv\",num_roads,pv_profile,zeta_pv_err_ratio))
        # ماتریس فیزیکی پروفایل مورد بررسی را از سناریو می‌خواند.
        mat = s[key]
        # ابعاد ماتریس یا بردار را با تعداد واحدها و ساعت‌های مورد انتظار تطبیق می‌دهد.
        size(mat) == (rows,num_tau) || error(\"Invalid shape of \$key\")
        # هر سطر واحد یا محل و هر ساعت ماتریس پروفایل را کنترل می‌کند.
        for r in 1:rows, h in Tau_set
            # مقدار خروجی واحد یا محل و ساعت جاری را برای کنترل دامنه می‌گیرد.
            v = mat[r,h]
            # در دورهٔ اول دامنهٔ خطا را صفر و در دوره‌های بعد متناسب با پروفایل پایه قرار می‌دهد.
            radius = t == 1 ? 0.0 : ratio*profile[h]
            # عضویت مقدار یا نمونه در دامنهٔ تعریف‌شده را با تلرانس مشخص کنترل می‌کند.
            isfinite(v) && abs(v-profile[h]) <= radius+atol || error(\"\$key[\$r,\$h] outside Phi_\$t\")
            # شرط غیرصفر بودن دامنهٔ خطای پروفایل با تلرانس عددی را بررسی می‌کند.
            if radius > atol
                # انحراف نرمال‌شدهٔ خروجی را برای کنترل قرارگرفتن روی یکی از سه مقدار مجاز محاسبه می‌کند.
                u = (v-profile[h])/radius
                # با کنترل صحیح‌بودن انحراف نرمال‌شده، آن را به سه مقدار منفی یک، صفر یا مثبت یک حاصل از اختلاف دو بیت محدود می‌کند.
                abs(u-round(u)) <= atol || error(\"\$key violates binary Eq. (52)\")
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # سازگاری فرادادهٔ دودویی اختیاری را نیز با سناریوی فیزیکی کنترل می‌کند.
    validate_uncertainty_metadata(t,s; atol)
    # موفقیت اعتبارسنجی تمام کنترل‌های طی‌شده را اعلام می‌کند.
    return true
# تعریف تابع validate_scenario را پایان می‌دهد.
end

# سازگاری بیت‌های ذخیره‌شدهٔ عدم‌قطعیت با مقادیر فیزیکی سناریو را بررسی می‌کند.
function validate_uncertainty_metadata(t,s; atol=1e-8)
    # نام چهار بیت رشد تقاضا و ظرفیت تجدیدپذیر را برای کنترل فراداده مشخص می‌کند.
    scalars=(\"omega_u_plus\",\"omega_u_minus\",\"omega_p_plus\",\"omega_p_minus\")
    # نام شش ماتریس بیت انحراف مثبت و منفی باد و دو نوع خورشیدی را مشخص می‌کند.
    arrays=(\"beta_wt_plus\",\"beta_wt_minus\",\"beta_pv_plus\",\"beta_pv_minus\",\"psi_plus\",\"psi_minus\")
    # بررسی می‌کند آیا سناریو اصلاً فرادادهٔ بیت‌های عدم‌قطعیت دارد.
    present=any(haskey(s,k) for k in (scalars...,arrays...))
    # در نبود فراداده، کنترل را به همان اعتبارسنجی مقادیر فیزیکی محدود می‌کند.
    present || return true
    # اگر فراداده وجود دارد، حضور هر چهار بیت رشد تقاضا و تجدیدپذیر را الزامی می‌کند.
    all(haskey(s,k) for k in scalars) || error(\"Incomplete growth uncertainty metadata\")
    # آزمون محلی نزدیک‌بودن مقدار متناهی به صفر یا یک را تعریف می‌کند.
    binary(v)=isfinite(v) && min(abs(v),abs(v-1)) <= atol
    # صحت دودویی‌بودن مقادیر و سازگاری طول کد حالت یا فراداده را کنترل می‌کند.
    all(binary(s[k]) for k in scalars) || error(\"Eq52: growth indicators must be binary\")
    # G7.3.1: the physical image alone cannot validate the two-bit encoding.
    s[\"omega_u_plus\"] + s[\"omega_u_minus\"] <= 1 + atol ||
        error(\"Eq52: transport growth indicators are not mutually exclusive\")
    s[\"omega_p_plus\"] + s[\"omega_p_minus\"] <= 1 + atol ||
        error(\"Eq52: renewable growth indicators are not mutually exclusive\")
    if theta_err[t] == 0.0
        abs(s[\"omega_u_plus\"]) <= atol && abs(s[\"omega_u_minus\"]) <= atol ||
            error(\"Eq52: inactive transport growth indicators must be zero\")
    end
    if zeta_err[t] == 0.0
        abs(s[\"omega_p_plus\"]) <= atol && abs(s[\"omega_p_minus\"]) <= atol ||
            error(\"Eq52: inactive renewable growth indicators must be zero\")
    end
    # مقدار فیزیکی یا حاصل‌ضرب ذخیره‌شده را با رابطهٔ محاسبه‌شده از بیت‌های سناریو تطبیق می‌دهد.
    abs(s[\"theta_t\"]-(theta_fc[t]+theta_err[t]*(s[scalars[1]]-s[scalars[2]]))) <= atol || error(\"Eq48 metadata mismatch\")
    # مقدار فیزیکی یا حاصل‌ضرب ذخیره‌شده را با رابطهٔ محاسبه‌شده از بیت‌های سناریو تطبیق می‌دهد.
    abs(s[\"zeta_t\"]-(zeta_fc[t]+zeta_err[t]*(s[scalars[3]]-s[scalars[4]]))) <= atol || error(\"Eq49 metadata mismatch\")
    # شرط سناریوی قطعی ریشه بدون فرادادهٔ ماتریسی انحراف را بررسی می‌کند.
    if t == 1 && !any(haskey(s,k) for k in arrays)
        # در ریشهٔ قطعی، همهٔ بیت‌های رشد را با تلرانس عددی صفر می‌خواهد.
        all(abs(s[k]) <= atol for k in scalars) || error(\"Stage 1 must be deterministic\")
        # موفقیت اعتبارسنجی تمام کنترل‌های طی‌شده را اعلام می‌کند.
        return true
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # حضور کامل شش ماتریس انحراف خروجی را در فرادادهٔ سناریو کنترل می‌کند.
    all(haskey(s,k) for k in arrays) || error(\"Incomplete output uncertainty metadata\")
    # هر زوج ماتریس بیت مثبت و منفی را همراه پروفایل فیزیکی و پارامترهای آن بررسی می‌کند.
    for (plus,minus,physical,rows,profile,ratio) in (
          # بیت‌های مثبت و منفی باد را به ماتریس فیزیکی باد و پارامترهای آن مرتبط می‌کند.
          (arrays[1],arrays[2],\"xi_wt\",num_wt,wt_profile,xi_wt_err_ratio),
          # بیت‌های مثبت و منفی خورشیدی شبکه را به مقادیر فیزیکی آن مرتبط می‌کند.
          (arrays[3],arrays[4],\"zeta_pv\",num_pv_pdn,pv_profile,zeta_pv_err_ratio),
          # بیت‌های مثبت و منفی خورشیدی ایستگاه‌ها را به پروفایل فیزیکی محل‌ها مرتبط می‌کند.
          (arrays[5],arrays[6],\"zeta_station_pv\",num_roads,pv_profile,zeta_pv_err_ratio))
        # ابعاد ماتریس یا بردار را با تعداد واحدها و ساعت‌های مورد انتظار تطبیق می‌دهد.
        size(s[plus]) == size(s[minus]) == (rows,num_tau) || error(\"Invalid uncertainty metadata shape\")
        # صحت دودویی‌بودن مقادیر و سازگاری طول کد حالت یا فراداده را کنترل می‌کند.
        all(binary,s[plus]) && all(binary,s[minus]) || error(\"Eq52: output indicators must be binary\")
        all(s[plus] .+ s[minus] .<= 1 + atol) ||
            error(\"Eq52: output indicators are not mutually exclusive (\$plus, \$minus)\")
        # Symbolic and enumerable Phi_t create no indicator for an inactive radius.
        for h in Tau_set
            if t == 1 || profile[h]*ratio == 0.0
                all(abs.(s[plus][:,h]) .<= atol) &&
                    all(abs.(s[minus][:,h]) .<= atol) ||
                    error(\"Eq52: inactive output indicators must be zero (\$plus, \$minus, h=\$h)\")
            end
        end
        # سازگاری بیت‌ها با مقدار فیزیکی هر واحد یا محل و ساعت را بررسی می‌کند.
        for r in 1:rows,h in Tau_set
            # مقدار فیزیکی مورد انتظار را مستقیماً از پروفایل پایه و اختلاف بیت‌های ذخیره‌شده بازسازی می‌کند.
            expected=profile[h]*(1+ratio*(s[plus][r,h]-s[minus][r,h]))
            # مقدار فیزیکی یا حاصل‌ضرب ذخیره‌شده را با رابطهٔ محاسبه‌شده از بیت‌های سناریو تطبیق می‌دهد.
            abs(s[physical][r,h]-expected) <= atol || error(\"Eq50/51 metadata mismatch\")
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # شرط وجود فرادادهٔ حاصل‌ضرب بیت‌های مثبت بادی را بررسی می‌کند.
    if haskey(s,\"varpi_wt_plus\")
        # ابعاد ماتریس یا بردار را با تعداد واحدها و ساعت‌های مورد انتظار تطبیق می‌دهد.
        size(s[\"varpi_wt_plus\"]) == (num_wt,num_tau) || error(\"Invalid Eq53 product shape\")
        # حاصل‌ضرب ذخیره‌شدهٔ بیت‌های بادی را برای هر واحد و ساعت کنترل می‌کند.
        for w in 1:num_wt,h in Tau_set
            # مقدار فیزیکی یا حاصل‌ضرب ذخیره‌شده را با رابطهٔ محاسبه‌شده از بیت‌های سناریو تطبیق می‌دهد.
            abs(s[\"varpi_wt_plus\"][w,h]-s[\"omega_p_plus\"]*s[\"beta_wt_plus\"][w,h]) <= atol || error(\"Eq53 product mismatch\")
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # موفقیت اعتبارسنجی تمام کنترل‌های طی‌شده را اعلام می‌کند.
    return true
# تعریف تابع validate_uncertainty_metadata را پایان می‌دهد.
end

# فضای نام جداگانهٔ هسته‌های کران‌سازی، C&CG، برش و تقریب بالایی را آغاز می‌کند.
module REVCSCertifiedCore
# وابستگی‌های مدل‌سازی، حل و جبر خطی هستهٔ مستقل را در فضای همین ماژول بارگذاری می‌کند.
using JuMP, HiGHS, LinearAlgebra
# رابط استاندارد وضعیت حل، جهت هدف و انواع قیود را با نام کوتاه MOI وارد می‌کند.
import MathOptInterface as MOI

# گزارش واقعی زمان حل و اندازهٔ هر زیرمسئله؛ تخصیص حافظه، حافظهٔ اوج نیست.
const SOLVER_TRACE = NamedTuple[]
function solve_tracked!(m; context=\"core\")
    measurement = @timed JuMP.optimize!(m)
    feasible = has_values(m) && primal_status(m) == MOI.FEASIBLE_POINT
    bound = try objective_bound(m) catch; objective_sense(m)==MOI.MIN_SENSE ? -Inf : Inf end
    push!(SOLVER_TRACE, (;context, sense=string(objective_sense(m)),
        termination=string(termination_status(m)), primal=string(primal_status(m)),
        variables=num_variables(m), constraints=num_constraints(m;count_variable_in_set_constraints=true),
        seconds=measurement.time, allocated_bytes=measurement.bytes,
        gc_seconds=measurement.gctime, incumbent=feasible ? objective_value(m) : NaN, bound))
    return nothing
end
# جواب مثبت فارکاس شاهد نقض است؛ فقدان شاهد مثبت به‌تنهایی پوشش دامنه را اثبات نمی‌کند.
function farkas_gate(status, feasible, incumbent, bound; tol=1e-8)
    feasible && isfinite(incumbent) && incumbent>tol && return :witness
    status==MOI.OPTIMAL && feasible && isfinite(bound) && bound<=tol &&
        incumbent<=tol && return :covered
    return :unresolved
end

# پارامترهای شبکهٔ محدود و وزن‌های کد دودویی ظرفیت را نگه می‌دارد.
struct BinaryGrid
    # فیلد lo را برای حد پایین شبکهٔ ظرفیت با نوع مشخص‌شده نگه می‌دارد.
    lo::Float64
    # فیلد step را برای فاصلهٔ دو نقطهٔ مجاور شبکهٔ ظرفیت با نوع مشخص‌شده نگه می‌دارد.
    step::Float64
    # فیلد last را برای بزرگ‌ترین اندیس صحیح مجاز شبکه با نوع مشخص‌شده نگه می‌دارد.
    last::Int
    # فیلد weights را برای وزن‌های صحیح توان دو برای کدگذاری ظرفیت با نوع مشخص‌شده نگه می‌دارد.
    weights::Vector{Int}

    # سازندهٔ شبکهٔ محدود ظرفیت و وزن‌های دودویی آن را تعریف می‌کند؛ شبکه جای تمام اعداد حقیقی را نمی‌گیرد.
    function BinaryGrid(lo, hi, step)
        # متناهی‌بودن دو حد و گام، مثبت‌بودن گام و ترتیب درست بازهٔ شبکه را کنترل می‌کند.
        all(isfinite,(lo,hi,step)) && step>0 && hi>=lo || error(\"Invalid grid\")
        # تعداد فاصله‌های شبکه بین دو سر بازه را به عدد صحیح تبدیل می‌کند.
        n=round(Int,(hi-lo)/step)
        # کنترل می‌کند حد بالای شبکه نیز با تعداد صحیح گام‌ها قابل نمایش باشد.
        isapprox(lo+n*step,hi;atol=1e-8,rtol=1e-10) || error(\"Grid must include both endpoints\")
        # وزن‌های کد دودویی را خالی و نخستین وزن را یک قرار می‌دهد.
        w=Int[]; p=1
        # تا وقتی مجموع وزن‌ها کل شبکه را پوشش نداده، وزن دودویی جدید تولید می‌کند.
        while sum(w)<n
            # وزن توان دو جاری را به کدگذاری شبکه اضافه می‌کند.
            push!(w,p)
            # پیش از دو برابر کردن وزن بیت، خطر سرریز عدد صحیح را کنترل می‌کند.
            p<=typemax(Int)÷2 || error(\"Grid too large\")
            # وزن بیت بعدی را دو برابر می‌کند.
            p*=2
        # تکرار شرطی ساخت وزن‌های دودویی را پایان می‌دهد.
        end
        # ساختار شبکه را با حد پایین، گام، آخرین اندیس و وزن‌های دودویی می‌سازد.
        new(Float64(lo),Float64(step),n,w)
    # تعریف تابع BinaryGrid را پایان می‌دهد.
    end
# تعریف ساختار BinaryGrid را پایان می‌دهد.
end

# تابع تبدیل مقدار واقعاً واقع بر شبکه به بیت‌های دودویی را تعریف می‌کند.
function encode(g::BinaryGrid,x)
    # متناهی‌بودن مقدار لازم برای ادامهٔ کران‌سازی را کنترل می‌کند؛ مقدار نامعلوم جایگزین عددی نمی‌شود.
    isfinite(x) || error(\"Nonfinite state\")
    # اندیس شبکهٔ نزدیک به مقدار ورودی را برای کنترل عضویت محاسبه می‌کند.
    k=round(Int,(x-g.lo)/g.step)
    # عضویت مقدار در بازه و شبکهٔ صریح را با تلرانس عددی می‌سنجد؛ مقدار خارج از شبکه را بی‌صدا گرد نمی‌کند.
    0<=k<=g.last && isapprox(g.lo+k*g.step,x;atol=1e-7,rtol=1e-10) || error(\"State not on specified grid\")
    # هر بیت اندیس شبکه را با تقسیم صحیح و باقیمانده استخراج می‌کند.
    return [Int((k÷w)%2) for w in g.weights]
# تعریف تابع encode را پایان می‌دهد.
end

# تابع بازیابی مقدار فیزیکی از بیت‌های یک کد مجاز را تعریف می‌کند.
function decode(g::BinaryGrid,b)
    # صحت دودویی‌بودن مقادیر و سازگاری طول کد حالت یا فراداده را کنترل می‌کند.
    length(b)==length(g.weights) && all(x->x==0||x==1,b) || error(\"Invalid bits\")
    # اندیس شبکه را از مجموع وزن‌دار بیت‌ها بازیابی می‌کند.
    k=dot(g.weights,b)
    # کدهای دودویی اضافی فراتر از آخرین نقطهٔ شبکه را نامعتبر اعلام می‌کند.
    k<=g.last || error(\"Unused binary code\")
    # اندیس شبکه را به مقدار فیزیکی ظرفیت برمی‌گرداند.
    return g.lo+g.step*k
# تعریف تابع decode را پایان می‌دهد.
end

# متغیرهای دودویی ظرفیت و رابطهٔ آن‌ها با مقدار فیزیکی را به مدل اضافه می‌کند.
function grid_variables!(m,g::BinaryGrid; physical=nothing)
    # به تعداد وزن‌های شبکه، متغیر دودویی ایجاد می‌کند.
    b=@variable(m,[1:length(g.weights)],Bin)
    # اندیس شبکه را به‌صورت عبارت خطی بیت‌ها تعریف می‌کند.
    k=@expression(m,sum(g.weights[j]*b[j] for j in eachindex(b)))
    # کدهای دودویی خارج از آخرین اندیس مجاز شبکه را حذف می‌کند.
    @constraint(m,k<=g.last)
    # ظرفیت فیزیکی متناظر با کد دودویی را تعریف می‌کند.
    x=@expression(m,g.lo+g.step*k)
    # در صورت ارائهٔ متغیر فیزیکی، آن را دقیقاً به مقدار شبکه متصل می‌کند.
    physical===nothing || @constraint(m,physical==x)
    # بردار بیت‌ها و عبارت ظرفیت فیزیکی را برمی‌گرداند.
    return b,x
# تعریف تابع grid_variables! را پایان می‌دهد.
end
# سازندهٔ مدل کمکی ساکت HiGHS را با شکاف هدف صفر و بودجهٔ زمان ورودی تعریف می‌کند.
new_model(; seconds=600.0)=begin
    # برای مدل کمکی، مهلت حل مثبت را الزامی می‌کند.
    seconds>0 || error(\"Positive solve time required\")
    # مدل عددی کمکی را با حل‌کنندهٔ HiGHS ایجاد می‌کند.
    m=Model(HiGHS.Optimizer)
    # خروجی معمول حل‌کنندهٔ مدل کمکی را غیرفعال می‌کند.
    set_silent(m)
    # مهلت حل مدل را به مقدار ورودی بر حسب ثانیه محدود می‌کند.
    set_time_limit_sec(m,Float64(seconds))
    # شکاف هدف MILP را صفر می‌گذارد؛ توقف زمانی همچنان با کران واقعی گزارش می‌شود.
    set_optimizer_attribute(m,\"mip_rel_gap\",0.0)
    # مدل تنظیم‌شده را به‌عنوان مقدار نهایی بلوک سازنده برمی‌گرداند.
    m
# بلوک چنددستوری یا مجموعه‌قیود را پایان می‌دهد.
end

# سازگاری مدل بدون متغیر با حل‌کننده را با یک متغیر ثابت صفر تأمین می‌کند.
function ensure_solver_column!(m)
    # فقط برای مدل بدون متغیر، یک ستون ثابت صفر اضافه می‌کند؛ هزینه و مجموعهٔ تصمیم مؤثر عوض نمی‌شود.
    num_variables(m)==0 && @variable(m,lower_bound=0.0,upper_bound=0.0)
    # مدل ساخته‌شده یا تنظیم‌شده را برای استفادهٔ فراخواننده برمی‌گرداند.
    return m
# تعریف تابع ensure_solver_column! را پایان می‌دهد.
end

# استخراج محتاطانهٔ کران پایین و بالای یک مدل کمینه‌سازی را تعریف می‌کند.
function min_bounds(m)
    # کمینه‌سازی‌بودن مدل را کنترل می‌کند تا جای کران پایین و بالا عوض نشود.
    objective_sense(m)==MOI.MIN_SENSE || error(\"Expected minimization\")
    # وضعیت توقف حل مدل کمینه‌سازی را استخراج می‌کند.
    st=termination_status(m)
    # در صورت اثبات عدم امکان، هر دو کران هزینهٔ آن پاسخ را مثبت بی‌نهایت ثبت می‌کند.
    st==MOI.INFEASIBLE && return (lower=Inf,upper=Inf,status=st,feasible=false)
    # پاسخ نامحدود یا وضعیت مبهم امکان‌پذیری را خطا می‌گیرد و به هزینهٔ متناهی تبدیل نمی‌کند.
    st in (MOI.DUAL_INFEASIBLE,MOI.INFEASIBLE_OR_UNBOUNDED) && error(\"Unbounded or ambiguous recourse\")
    # وجود جواب با وضعیت اولیهٔ قابل قبول را کنترل می‌کند؛ جواب تقریبی فاقد این وضعیت پذیرفته نمی‌شود.
    feasible=has_values(m) && primal_status(m)==MOI.FEASIBLE_POINT
    # کران پایین حل‌کنندهٔ کمینه‌سازی را می‌خواند؛ فقدان کران را با منفی بی‌نهایت نشان می‌دهد.
    lo=try objective_bound(m) catch; -Inf end
    # جواب قابل قبول کمینه‌سازی را کران بالا می‌گیرد؛ بدون جواب، کران بالا بی‌نهایت است.
    hi=feasible ? objective_value(m) : Inf
    # کران عددی نامعتبر را به کران محافظه‌کارانهٔ منفی بی‌نهایت تبدیل می‌کند.
    isnan(lo) && (lo=-Inf)
    # شرط متناهی‌بودن هر دو کران را بررسی می‌کند.
    if isfinite(lo)&&isfinite(hi)
        # ترتیب صحیح کران پایین و بالا را با تلرانس عددی کنترل می‌کند و ناسازگاری را خطا می‌گیرد.
        lo<=hi+1e-7*max(1.0,abs(lo),abs(hi)) || error(\"Crossed minimization bounds\")
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # دو کران، وضعیت توقف و وجود جواب قابل قبول را برمی‌گرداند.
    return (lower=lo,upper=hi,status=st,feasible)
# تعریف تابع min_bounds را پایان می‌دهد.
end

# الگوی کامل تمام تصمیم‌های صحیح یک جواب پاسخ را نگه می‌دارد.
struct IntegerPattern
    # فیلد indices را برای شناسهٔ متغیرهای صحیح در ترتیب ساخت مدل با نوع مشخص‌شده نگه می‌دارد.
    indices::Vector{Int}
    # فیلد values را برای مقادیر صحیح تثبیت‌شدهٔ الگو با نوع مشخص‌شده نگه می‌دارد.
    values::Vector{Int}
# تعریف ساختار IntegerPattern را پایان می‌دهد.
end

# استخراج تمام تصمیم‌های صحیح و دودویی جواب قابل قبول را تعریف می‌کند.
function integer_pattern(m)
    # الگوی صحیح را فقط از جواب واقعاً قابل قبول استخراج می‌کند.
    has_values(m) && primal_status(m)==MOI.FEASIBLE_POINT || error(\"No feasible integer pattern\")
    # تمام متغیرهای صحیح و دودویی، شامل تصمیم‌های بهره‌برداری و سرمایه‌گذاری، را انتخاب می‌کند.
    vs=filter(v->is_binary(v)||is_integer(v),all_variables(m))
    # مقادیر جواب صحیح را پس از استخراج به عدد صحیح گرد می‌کند؛ صحت نزدیکی در خط بعد کنترل می‌شود.
    vals=round.(Int,value.(vs))
    # نزدیکی جواب به مقدار صحیح یا دودویی را کنترل می‌کند تا جواب کسری به ستون یا سناریوی صحیح تبدیل نشود.
    maximum(abs.(value.(vs).-vals);init=0.0)<=1e-5 || error(\"Nonintegral incumbent\")
    # شناسه‌ها و مقادیر همهٔ تصمیم‌های صحیح را در یک الگو ذخیره می‌کند.
    return IntegerPattern([index(v).value for v in vs],vals)
# تعریف تابع integer_pattern را پایان می‌دهد.
end
# کلید متنی الگو را می‌سازد تا از هزینهٔ نوع‌دهی به چندتایی‌های بسیار بزرگ جلوگیری شود.
pattern_key(p::IntegerPattern)=join(p.indices,\",\")*\":\"*join(p.values,\",\")
# بردار بیت را به کلید متنی یکتا در طول ثابت تبدیل می‌کند.
binary_key(b)=join(b)

# تمام متغیرهای صحیح الگو را تثبیت می‌کند تا زیرمسئلهٔ پیوستهٔ همان الگو به دست آید.
function fix_pattern!(m,p::IntegerPattern)
    # تمام متغیرهای صحیح و دودویی، شامل تصمیم‌های بهره‌برداری و سرمایه‌گذاری، را انتخاب می‌کند.
    vs=filter(v->is_binary(v)||is_integer(v),all_variables(m))
    # شناسه و ترتیب تمام متغیرهای صحیح را میان سناریوها ثابت می‌خواهد تا مقادیر ستون به متغیر اشتباه اعمال نشوند.
    [index(v).value for v in vs]==p.indices || error(\"Builder changed integer layout across uncertainty\")
    # هر متغیر صحیح را همراه مقدار همان ستون برای تثبیت دقیق پردازش می‌کند.
    for (v,k) in zip(vs,p.values)
        # حد پایین صریح متغیر صحیح را پیش از تثبیت نگه می‌دارد.
        lo=has_lower_bound(v) ? lower_bound(v) : -Inf
        # حد بالای صریح متغیر صحیح را پیش از تثبیت نگه می‌دارد.
        hi=has_upper_bound(v) ? upper_bound(v) : Inf
        # برای متغیر دودویی، حدود ضمنی صفر و یک را نیز لحاظ می‌کند.
        is_binary(v) && (lo=max(lo,0.0);hi=min(hi,1.0))
        # ناسازگاری مقدار الگو با حدود یا تثبیت قبلی متغیر را پیش از اعمال force تشخیص می‌دهد.
        invalid=k<lo-1e-8 || k>hi+1e-8 || (is_fixed(v)&&abs(fix_value(v)-k)>1e-8)
        # اگر الگو با حدود مدل ناسازگار باشد، یک قید ناسازگار اضافه می‌کند تا LP به‌درستی ناممکن بماند.
        invalid && @constraint(m,0.0*v==1.0)
        # شرط دودویی‌بودن متغیر الگوی تثبیت‌شده را بررسی می‌کند.
        if is_binary(v)
            # صحت دودویی‌بودن مقادیر و سازگاری طول کد حالت یا فراداده را کنترل می‌کند.
            k in (0,1) || error(\"Invalid binary pattern\")
            # نوع دودویی متغیر را پیش از تثبیت عددی حذف می‌کند.
            unset_binary(v)
        # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
        else
            # نوع صحیح متغیر را پیش از تثبیت عددی حذف می‌کند.
            unset_integer(v)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # متغیر را به مقدار این الگوی صحیح تثبیت می‌کند؛ این کار ریلکسیشن آزاد MILP نیست.
        fix(v,Float64(k);force=true)
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # مدل ساخته‌شده یا تنظیم‌شده را برای استفادهٔ فراخواننده برمی‌گرداند.
    return m
# تعریف تابع fix_pattern! را پایان می‌دهد.
end

# تکرارگرساز و تعداد دقیق اعضای یک دامنهٔ مشخص عدم‌قطعیت را نگه می‌دارد.
struct UncertaintyDomain
    # فیلد factory را برای تابعی که در هر فراخوانی تکرارگر تازهٔ دامنه را می‌سازد با نوع مشخص‌شده نگه می‌دارد.
    factory::Function
    # فیلد cardinality را برای تعداد دقیق اعضای دامنه با عدد صحیح با طول دلخواه با نوع مشخص‌شده نگه می‌دارد.
    cardinality::BigInt
    # فیلد scope را برای شناسهٔ مدل و دامنه‌ای که نتیجه برای آن معتبر است با نوع مشخص‌شده نگه می‌دارد.
    scope::String

    # سازندهٔ دامنهٔ تکرارپذیر عدم‌قطعیت با تعداد دقیق و شناسهٔ دامنه را تعریف می‌کند.
    function UncertaintyDomain(factory,n,scope)
        # دامنهٔ عدم‌قطعیت با تعداد اعضای صفر یا منفی را نمی‌پذیرد.
        n>0 || error(\"Empty uncertainty domain\")
        # تکرارگرساز، تعداد دقیق اعضا و شناسهٔ دامنه را ذخیره می‌کند.
        new(factory,BigInt(n),String(scope))
    # تعریف تابع UncertaintyDomain را پایان می‌دهد.
    end
# تعریف ساختار UncertaintyDomain را پایان می‌دهد.
end

# کران‌ها، نقش هزینهٔ آینده، شاهد، ستون‌ها و علت توقف C&CG را نگه می‌دارد.
struct CCGResult
    # فیلد lower را برای کران پایین مسئلهٔ دارای نقش ثبت‌شده با نوع مشخص‌شده نگه می‌دارد.
    lower::Float64
    # فیلد upper را برای کران بالای مسئلهٔ دارای نقش ثبت‌شده با نوع مشخص‌شده نگه می‌دارد.
    upper::Float64
    # فیلد converged را برای پرچم بسته‌شدن شکاف در حدود دقت تعیین‌شده با نوع مشخص‌شده نگه می‌دارد.
    converged::Bool
    # فیلد infeasible را برای پرچم اثبات عدم امکان پاسخ‌گویی مقاوم با نوع مشخص‌شده نگه می‌دارد.
    infeasible::Bool
    # فیلد scenario را برای سناریوی شاهد ثبت‌شده برای کران پایین با نوع مشخص‌شده نگه می‌دارد.
    scenario::Any
    # فیلد columns را برای فهرست الگوهای کامل تصمیم‌های صحیح با نوع مشخص‌شده نگه می‌دارد.
    columns::Vector{IntegerPattern}
    # فیلد history را برای تاریخچهٔ کران‌ها و مرحلهٔ حل در هر تکرار با نوع مشخص‌شده نگه می‌دارد.
    history::Vector{NamedTuple}
    # فیلد scope را برای شناسهٔ مدل و دامنه‌ای که نتیجه برای آن معتبر است با نوع مشخص‌شده نگه می‌دارد.
    scope::String
    # فیلد reason را برای علت توقف یا وضعیت نهایی الگوریتم با نوع مشخص‌شده نگه می‌دارد.
    reason::Symbol
    # فیلد bound_role را برای نقش هزینهٔ آینده: دقیق، تقریب پایین یا تقریب بالا با نوع مشخص‌شده نگه می‌دارد.
    bound_role::Symbol
# تعریف ساختار CCGResult را پایان می‌دهد.
end
# بسته‌شدن شکاف دو کران متناهی را با مقیاس هزینه کنترل می‌کند.
gap_closed(lo,hi,tol)=isfinite(lo)&&isfinite(hi)&&hi-lo<=tol*max(1.0,abs(lo),abs(hi))

# ترکیب کران‌های معتبر پایین و بالا برای یک هدف و نقش یکسان را تعریف می‌کند.
function certified_gap(lower::CCGResult,upper::CCGResult;rtol=0.001)
    # همسانی شناسهٔ هدف هزینه را کنترل می‌کند تا گواه مدل، دوره یا نسخهٔ دیگری استفاده نشود.
    lower.scope==upper.scope || error(\"Different cost-to-go targets\")
    # نقش کران یا تقریب آینده را کنترل می‌کند تا کران حل یک تقریب به‌جای گواه مسئلهٔ اصلی گزارش نشود.
    lower.bound_role in (:exact,:lower) || error(\"Upper-envelope LB is not a true model lower bound\")
    # نقش کران یا تقریب آینده را کنترل می‌کند تا کران حل یک تقریب به‌جای گواه مسئلهٔ اصلی گزارش نشود.
    upper.bound_role in (:exact,:upper) || error(\"Lower-envelope UB is not a true model upper bound\")
    # از حل دارای نقش پایین، کران پایین و از حل دارای نقش بالا، کران بالا را انتخاب می‌کند.
    lo=lower.lower;hi=upper.upper
    # شرط متناهی‌بودن هر دو کران را بررسی می‌کند.
    if isfinite(lo)&&isfinite(hi)
        # ترتیب صحیح کران پایین و بالا را با تلرانس عددی کنترل می‌کند و ناسازگاری را خطا می‌گیرد.
        lo<=hi+1e-7*max(1.,abs(lo),abs(hi)) || error(\"Global grid-model bounds cross\")
        # شکاف نسبی دو گواه مربوط به هدف مشترک را محاسبه می‌کند.
        gap=max(0.,hi-lo)/max(1.,abs(lo),abs(hi))
        # کران‌های مشترک و وضعیت شکاف را بدون ارتقای نتیجهٔ ناتمام به گواه همگرایی برمی‌گرداند.
        return (;lower=lo,upper=hi,gap,converged=gap<=rtol,scope=lower.scope)
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # کران‌های مشترک و وضعیت شکاف را بدون ارتقای نتیجهٔ ناتمام به گواه همگرایی برمی‌گرداند.
    return (;lower=lo,upper=hi,gap=Inf,converged=false,scope=lower.scope)
# تعریف تابع certified_gap را پایان می‌دهد.
end

# نسخهٔ مرجع C&CG با پیمایش سناریوهای دامنه را تعریف می‌کند؛ پیمایش ناقص کران بالای سراسری نمی‌دهد.
function solve_ccg(builder,domain::UncertaintyDomain; max_iters=100,
        # بودجهٔ پیمایش، تلرانس شکاف، زمان هر حل و نقش تقریب هزینه را ورودی اختیاری قرار می‌دهد.
        max_master_scenarios=10000,rtol=0.001,seconds=600.0,bound_role=:exact)
    # بودجهٔ مثبت تکرار و پیمایش و تلرانس نسبی مجاز C&CG مرجع را کنترل می‌کند.
    max_iters>0 && max_master_scenarios>0 && 0<=rtol<1 || error(\"Invalid C&CG budget\")
    # نقش کران یا تقریب آینده را کنترل می‌کند تا کران حل یک تقریب به‌جای گواه مسئلهٔ اصلی گزارش نشود.
    bound_role in (:exact,:lower,:upper) || error(\"Invalid cost-envelope role\")
    # فهرست ستون‌های C&CG را ابتدا خالی ایجاد می‌کند.
    columns=IntegerPattern[]
    # مجموعهٔ کلید الگوهای دیده‌شده را برای جلوگیری از افزودن تکراری ایجاد می‌کند.
    keys_seen=Set{String}()
    # تاریخچهٔ حل را به‌صورت سطرهای نام‌دار خالی آغاز می‌کند.
    history=NamedTuple[]
    # بدون گواه اولیه، کران پایین را منفی و کران بالا را مثبت بی‌نهایت قرار می‌دهد.
    lower=-Inf;upper=Inf
    # اولین سناریوی تکرارگر تازهٔ دامنه را برای آغاز C&CG می‌گیرد.
    first_entry=iterate(domain.factory())
    # تعداد اعضای واقعاً تولیدشده را با تعداد دقیق اعلام‌شدهٔ دامنه تطبیق می‌دهد.
    first_entry===nothing && error(\"Domain cardinality disagrees with empty iterator\")
    # سناریوی نخست را نامزد حل داخلی قرار می‌دهد.
    candidate=first_entry[1]
    # شاهد اولیهٔ کران پایین را با سناریوی آغازین مقداردهی می‌کند.
    best_scenario=candidate
    # علت توقف پیش‌فرض را رسیدن به سقف تکرار قرار می‌دهد.
    reason=:iteration_limit
    # روی تکرارهای مجاز الگوریتم تا سقف تعیین‌شده حلقه می‌زند.
    for iteration in 1:max_iters
        # مدل داخلی MILP را در سناریوی نامزد می‌سازد و سازگاری مدل بی‌متغیر را کنترل می‌کند.
        m=ensure_solver_column!(builder(candidate))
        # مهلت حل مدل را به مقدار ورودی بر حسب ثانیه محدود می‌کند.
        set_time_limit_sec(m,Float64(seconds))
        # MILP پاسخ را در سناریوی منتخب حل می‌کند؛ تمام متغیرهای صحیح همچنان فعال هستند.
        solve_tracked!(m)
        # کران‌های واقعی حل داخلی را می‌خواند؛ صرف وجود جواب را بهینه‌بودن فرض نمی‌کند.
        inner=min_bounds(m)
        # شرط اثبات ناممکن‌بودن مدل پاسخ در سناریوی جاری را بررسی می‌کند.
        if inner.status==MOI.INFEASIBLE
            # An UPPER codebook can exclude otherwise feasible physical recourse.
            # Do not promote UPPER-restricted infeasibility to full physical infeasibility.
            if bound_role==:upper
                return CCGResult(lower,Inf,false,false,candidate,columns,history,
                    domain.scope,:upper_codebook_or_physical_infeasible,bound_role)
            end
            # کشف سناریوی ناممکن و تعداد ستون‌های موجود را در تاریخچه ثبت می‌کند.
            push!(history,(;iteration,lower=Inf,upper=Inf,master_complete=false,columns=length(columns)))
            # اثبات ناممکن‌بودن پاسخ در یک سناریوی مجاز را به‌عنوان عدم امکان مقاوم ثبت می‌کند.
            return CCGResult(Inf,Inf,false,true,candidate,columns,history,domain.scope,:robust_infeasible,bound_role)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # شرط بهترشدن کران پایین مقاوم در سناریوی جاری را بررسی می‌کند.
        if inner.lower>lower
            # کران پایین مقاوم و سناریوی شاهد آن را با گواه بهتر به‌روز می‌کند.
            lower=inner.lower;best_scenario=candidate
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # در نبود جواب قابل قبول داخلی، بدون ادعای همگرایی نتیجهٔ جزئی را برمی‌گرداند.
        inner.feasible || return CCGResult(lower,upper,false,false,best_scenario,
            # علت توقف نبود جواب داخلی را با تاریخچه، دامنه و نقش هزینه در نتیجه تکمیل می‌کند.
            columns,history,domain.scope,:inner_no_incumbent,bound_role)
        # تمام تصمیم‌های صحیح جواب داخلی را برای ستون جدید استخراج می‌کند.
        p=integer_pattern(m)
        # کلید یکتای الگوی صحیح جدید را می‌سازد.
        key=pattern_key(p)
        # جدیدبودن الگوی صحیح را بررسی می‌کند.
        fresh=!(key in keys_seen)
        # شرط جدیدبودن الگوی تمام تصمیم‌های صحیح را بررسی می‌کند.
        if fresh
            # الگوی جدید و کلید آن را در فهرست ستون‌ها ثبت می‌کند.
            push!(columns,p);push!(keys_seen,key)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # شمار سناریوهای بررسی‌شده در مستر مرجع را صفر می‌کند.
        scanned=0
        # بیشترین هزینهٔ محدودشده به ستون‌ها را پیش از پیمایش مقداردهی می‌کند.
        master_upper=-Inf
        # سناریوی بیشینه‌کنندهٔ مستر را ابتدا نامشخص می‌گذارد.
        selected=nothing
        # تا بررسی تمام اعضای دامنه، مستر پیمایشی را کامل فرض نمی‌کند.
        complete=false
        # روی سناریوهای تکرارگر تازهٔ دامنهٔ عدم‌قطعیت حلقه می‌زند.
        for u in domain.factory()
            # پس از رسیدن به بودجهٔ پیمایش توقف می‌کند؛ این توقف اجازهٔ ساخت کران بالای سراسری نمی‌دهد.
            scanned>=max_master_scenarios && break
            # شمار سناریوهای واقعاً پیمایش‌شده را افزایش می‌دهد.
            scanned+=1
            # کران بالای هزینه در این سناریو را پیش از بررسی ستون‌ها بی‌نهایت قرار می‌دهد.
            point_upper=Inf
            # روی تمام الگوهای صحیح موجود در مستر حلقه می‌زند.
            for col in columns
                # مدل سناریوی جاری را برای ارزیابی الگوی صحیح می‌سازد.
                lp=ensure_solver_column!(builder(u))
                # تمام تصمیم‌های صحیح ستون را تثبیت می‌کند تا هزینهٔ LP همان الگو بررسی شود.
                fix_pattern!(lp,col)
                # مهلت حل LP الگوی صحیح تثبیت‌شده را بر حسب ثانیه تعیین می‌کند.
                set_time_limit_sec(lp,Float64(seconds))
                # LP پاسخِ همان سناریو و همان الگوی صحیح را حل می‌کند.
                solve_tracked!(lp)
                # کران‌ها و وضعیت LP الگوی تثبیت‌شده را استخراج می‌کند.
                lp_bounds=min_bounds(lp)
                # بهترین کران بالای هزینه بین ستون‌های موجود در این سناریو را نگه می‌دارد.
                point_upper=min(point_upper,lp_bounds.upper)
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
            # شرط وجود نخستین سناریو یا بدترشدن هزینهٔ محدود به ستون‌ها را بررسی می‌کند.
            if selected===nothing || point_upper>master_upper
                # بیشترین کران هزینهٔ سناریوهای پیمایش‌شده و سناریوی متناظر را نگه می‌دارد.
                master_upper=point_upper;selected=u
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # تعداد اعضای واقعاً تولیدشده را با تعداد دقیق اعلام‌شدهٔ دامنه تطبیق می‌دهد.
        BigInt(scanned)<=domain.cardinality || error(\"Iterator exceeds declared cardinality\")
        # تعداد اعضای واقعاً تولیدشده را با تعداد دقیق اعلام‌شدهٔ دامنه تطبیق می‌دهد.
        BigInt(scanned)==min(BigInt(max_master_scenarios),domain.cardinality) || error(\"Iterator ended before declared cardinality\")
        # شرط پیمایش دقیق همهٔ سناریوهای دامنهٔ تعریف‌شده را بررسی می‌کند.
        if BigInt(scanned)==domain.cardinality
            # شمارش مستقل اعضای دامنه را با عدد صحیح با طول دلخواه آغاز می‌کند.
            actual=BigInt(0)
            # روی تمام اعضای دامنه برای کنترل مستقل تعداد حلقه می‌زند.
            for _ in domain.factory()
                # یک عضو واقعی دامنه را در کنترل مستقل تعداد می‌شمارد.
                actual+=1
                # تعداد اعضای واقعاً تولیدشده را با تعداد دقیق اعلام‌شدهٔ دامنه تطبیق می‌دهد.
                actual>domain.cardinality && error(\"Incorrect domain cardinality\")
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
            # تعداد اعضای واقعاً تولیدشده را با تعداد دقیق اعلام‌شدهٔ دامنه تطبیق می‌دهد.
            actual==domain.cardinality || error(\"Incorrect domain cardinality\")
            # پس از کنترل شمارش کامل، مستر پیمایشی را کامل علامت می‌زند.
            complete=true
            # کران بالای معتبر جدید را با بهترین کران بالای قبلی ترکیب می‌کند.
            upper=min(upper,master_upper)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # شرط وجود هم‌زمان کران پایین و بالای متناهی مقاوم را بررسی می‌کند.
        if isfinite(lower)&&isfinite(upper)
            # ترتیب صحیح کران پایین و بالا را با تلرانس عددی کنترل می‌کند و ناسازگاری را خطا می‌گیرد.
            lower<=upper+1e-7*max(1.0,abs(lower),abs(upper)) || error(\"C&CG bounds cross\")
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # کران‌های این تکرار، کامل‌بودن مستر و تعداد ستون‌ها را در تاریخچه ذخیره می‌کند.
        push!(history,(;iteration,lower,upper,master_complete=complete,columns=length(columns)))
        # شرط بسته‌شدن شکاف نسبی دو کران معتبر را بررسی می‌کند.
        if gap_closed(lower,upper,rtol)
            # کران‌ها، شاهد، تاریخچه و علت توقف C&CG را با همان نقش و دامنهٔ ثبت‌شده برمی‌گرداند.
            return CCGResult(lower,upper,true,false,best_scenario,columns,history,domain.scope,:gap,bound_role)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # شرط ناقص‌ماندن پیمایش مستر مرجع را بررسی می‌کند.
        if !complete
            # ناتمام‌بودن مستر به‌دلیل بودجهٔ پیمایش را علت توقف ثبت می‌کند.
            reason=:master_scan_budget
            # حلقهٔ جاری را با علت یا وضعیت ثبت‌شده متوقف می‌کند.
            break
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # شرط تکرار همان الگوی صحیح و همان سناریو بدون پیشرفت را بررسی می‌کند.
        if !fresh && selected==candidate
            # تکرار همان ستون و سناریو را محدودیت دقت حل ثبت می‌کند؛ همگرایی فرض نمی‌شود.
            reason=:solver_accuracy_limit
            # حلقهٔ جاری را با علت یا وضعیت ثبت‌شده متوقف می‌کند.
            break
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # سناریوی انتخابی مستر را به حل داخلی تکرار بعد می‌فرستد.
        candidate=selected
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # کران‌ها، شاهد، تاریخچه و علت توقف C&CG را با همان نقش و دامنهٔ ثبت‌شده برمی‌گرداند.
    return CCGResult(lower,upper,false,false,best_scenario,columns,history,domain.scope,reason,bound_role)
# تعریف تابع solve_ccg را پایان می‌دهد.
end

# ضرایب و گواه‌های برش پایین لاگرانژی در فضای حالت دودویی را نگه می‌دارد.
struct BinaryCut
    # فیلد intercept را برای عرض از مبدأ برش لاگرانژی معتبر با نوع مشخص‌شده نگه می‌دارد.
    intercept::Float64
    # فیلد slope را برای بردار ضرایب برش در فضای حالت دودویی با نوع مشخص‌شده نگه می‌دارد.
    slope::Vector{Float64}
    # فیلد anchor_lower را برای کران پایین مقدار دوگان در حالت مرجع با نوع مشخص‌شده نگه می‌دارد.
    anchor_lower::Float64
    # فیلد anchor_upper را برای کران بالای گواه مقدار دوگان در حالت مرجع با نوع مشخص‌شده نگه می‌دارد.
    anchor_upper::Float64
    # فیلد converged را برای پرچم بسته‌شدن شکاف در حدود دقت تعیین‌شده با نوع مشخص‌شده نگه می‌دارد.
    converged::Bool
    # فیلد scope را برای شناسهٔ مدل و دامنه‌ای که نتیجه برای آن معتبر است با نوع مشخص‌شده نگه می‌دارد.
    scope::String
# تعریف ساختار BinaryCut را پایان می‌دهد.
end

# ساخت برش لاگرانژی در فضای حالت دودویی با روش سطح و تصویر L1 را تعریف می‌کند.
function lagrangian_cut(builder,anchor; max_iters=100,rtol=1e-6,seconds=600.0,scope=\"unscoped\")
    # صحت دودویی‌بودن مقادیر و سازگاری طول کد حالت یا فراداده را کنترل می‌کند.
    all(b->b==0||b==1,anchor) || error(\"Binary anchor required\")
    # روش سطح را فقط با سقف تکرار مثبت اجرا می‌کند.
    max_iters>0 || error(\"Positive level iterations required\")
    # مدل دارای تمام نسخه‌های دودویی حالت قبلی را برای مسئلهٔ لاگرانژی می‌سازد.
    m,beta=builder()
    # صحت دودویی‌بودن مقادیر و سازگاری طول کد حالت یا فراداده را کنترل می‌کند.
    length(beta)==length(anchor) && all(is_binary,beta) || error(\"All predecessor copies must be binary\")
    # تابع هدف اصلی را پیش از افزودن ضرایب لاگرانژ نگه می‌دارد.
    f=objective_function(m)
    # برای گرفتن شاهد هزینه در نقطهٔ مرجع، تمام بیت‌های حالت قبلی را موقتاً تثبیت می‌کند.
    for (b,k) in zip(beta,anchor);fix(b,Float64(k);force=true);end
    # MILP پاسخ را با وضعیت فعلی بیت‌های مرجع یا ضرایب لاگرانژ حل می‌کند.
    solve_tracked!(m)
    # کران‌های حل در حالت مرجع تثبیت‌شده را می‌گیرد.
    fixed=min_bounds(m)
    # وجود جواب قابل قبول در حالت مرجع را برای کران بالای گواه دوگان الزامی می‌کند.
    fixed.feasible || error(\"No feasible anchor for Lagrangian upper witness\")
    # هزینهٔ جواب قابل قبول مرجع را کران بالای مقدار دوگان قرار می‌دهد.
    anchor_upper=fixed.upper
    # تثبیت نقطهٔ مرجع را آزاد می‌کند تا نسخه‌های حالت قبلی در مسئلهٔ لاگرانژی تصمیم باشند.
    for b in beta;unfix(b);end
    # مدل کمکی روش سطح را با همان بودجهٔ زمان می‌سازد.
    master=new_model(;seconds)
    # تعداد بیت‌های حالت قبلی را می‌گیرد.
    n=length(beta)
    # ضرایب لاگرانژ را آزاد و بدون شعاع یا کران حدسی تعریف می‌کند.
    pi=@variable(master,[1:n])
    # متغیر مقدار دوگان را فقط با کران گواه هزینهٔ مرجع محدود می‌کند.
    eta=@variable(master,upper_bound=anchor_upper)
    # متغیرهای فاصلهٔ قدرمطلق برای تصویر L1 ضرایب را می‌سازد.
    distance=@variable(master,[1:n],lower_bound=0.0)
    # نقطهٔ آزمایشی ضرایب و مرکز روش سطح را صفر آغاز می‌کند.
    trial=zeros(n);center=zeros(n)
    # بهترین مقدار دوگان و برش را تا دریافت گواه معتبر نامشخص نگه می‌دارد.
    best=-Inf;intercept=-Inf;slope=zeros(n)
    # کران بالای اولیهٔ دوگان را از شاهد قابل قبول نقطهٔ مرجع می‌گیرد.
    dual_upper=anchor_upper
    # روی گام‌های مجاز روش سطح تا سقف تعیین‌شده حلقه می‌زند.
    for _ in 1:max_iters
        # هدف لاگرانژی را با ضرایب آزمایشی و نسخه‌های آزاد حالت قبلی می‌سازد.
        @objective(m,Min,f-sum(trial[j]*beta[j] for j in 1:n))
        # مهلت حل مدل را به مقدار ورودی بر حسب ثانیه محدود می‌کند.
        set_time_limit_sec(m,Float64(seconds))
        # MILP پاسخ را با وضعیت فعلی بیت‌های مرجع یا ضرایب لاگرانژ حل می‌کند.
        solve_tracked!(m)
        # کران پایین حل MILP لاگرانژی و هزینهٔ جواب قابل قبول آن را می‌خواند.
        row=min_bounds(m)
        # شرط بهترشدن گواه پایین دوگان با ضرایب آزمایشی جاری را بررسی می‌کند.
        if isfinite(row.lower) && row.lower+dot(trial,anchor)>best
            # ارزش گواه پایین دوگان در حالت مرجع را به‌روز می‌کند.
            best=row.lower+dot(trial,anchor)
            # عرض از مبدأ معتبر و شیب برش بهتر را همراه مرکز روش سطح نگه می‌دارد.
            intercept=row.lower;slope=copy(trial);center=copy(trial)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # اگر جواب قابل قبول برای ساخت شاهد دوگان موجود نباشد، روش سطح را متوقف می‌کند.
        row.feasible || break
        # بیت‌های جواب قابل قبول و هزینهٔ اصلی آن را برای برش بالایی دوگان می‌گیرد.
        witness=value.(beta);fw=value(f)
        # تابع افاین حاصل از جواب قابل قبول را به‌عنوان کران بالای تابع دوگان اضافه می‌کند.
        @constraint(master,eta<=fw+sum(pi[j]*(anchor[j]-witness[j]) for j in 1:n))
        # مدل برش‌های دوگان را برای بهبود کران بالا بیشینه می‌کند.
        @objective(master,Max,eta)
        # مدل کمکی روش سطح را با تابع هدف فعلی، برای کران دوگان یا تصویر L1، حل می‌کند.
        solve_tracked!(master)
        # تنها با حل بهینهٔ مدل کمکی، روش سطح را ادامه می‌دهد.
        termination_status(master)==MOI.OPTIMAL || break
        # کران بالای دوگان را با کران گواه مدل کمکی تنگ‌تر می‌کند.
        dual_upper=min(dual_upper,objective_bound(master))
        # در صورت بسته‌شدن شکاف دوگان، روش سطح را خاتمه می‌دهد.
        gap_closed(best,dual_upper,rtol) && break
        # بدون گواه پایین متناهی، محاسبهٔ سطح جدید را ادامه نمی‌دهد.
        isfinite(best) || break
        # سطح هدف را وسط کران پایین و بالای فعلی دوگان قرار می‌دهد.
        level=(best+dual_upper)/2
        # قید موقت رسیدن به سطح هدف را اضافه و مرجع آن را ثبت می‌کند.
        refs=ConstraintRef[@constraint(master,eta>=level)]
        # روی تمام مؤلفه‌های بردار دودویی حلقه می‌زند.
        for j in 1:n
            # نیمهٔ مثبت قدرمطلق فاصلهٔ ضریب از مرکز را خطی می‌کند.
            push!(refs,@constraint(master,distance[j]>=pi[j]-center[j]))
            # نیمهٔ منفی قدرمطلق فاصلهٔ ضریب از مرکز را خطی می‌کند.
            push!(refs,@constraint(master,distance[j]>=center[j]-pi[j]))
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # نزدیک‌ترین ضرایب به مرکز را در نرم L1 و با رعایت سطح هدف پیدا می‌کند.
        @objective(master,Min,sum(distance))
        # مدل کمکی روش سطح را با تابع هدف فعلی، برای کران دوگان یا تصویر L1، حل می‌کند.
        solve_tracked!(master)
        # بهینه‌بودن و قابل قبول بودن جواب مسئلهٔ تصویر روی سطح را هم‌زمان کنترل می‌کند.
        ok=termination_status(master)==MOI.OPTIMAL && primal_status(master)==MOI.FEASIBLE_POINT
        # فقط با جواب بهینه و قابل قبول تصویر، ضرایب آزمایشی بعدی را می‌گیرد.
        ok && (trial=value.(pi))
        # قیود موقت سطح و فاصله را پس از تصویر حذف می‌کند.
        foreach(c->delete(master,c),refs)
        # اگر تصویر روی سطح به جواب بهینهٔ قابل قبول نرسد، روش سطح را متوقف می‌کند.
        ok || break
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # متناهی‌بودن مقدار لازم برای ادامهٔ کران‌سازی را کنترل می‌کند؛ مقدار نامعلوم جایگزین عددی نمی‌شود.
    isfinite(intercept) || error(\"No finite Lagrangian lower cut\")
    # برش پایین معتبر و کران‌های مقدار آن در مرجع را همراه وضعیت همگرایی و شناسهٔ هدف برمی‌گرداند.
    return BinaryCut(intercept,slope,best,dual_upper,gap_closed(best,dual_upper,rtol),String(scope))
# تعریف تابع lagrangian_cut را پایان می‌دهد.
end

# حالت دودویی و کران بالای گواه هزینهٔ آیندهٔ همان حالت را نگه می‌دارد.
struct UpperSample
    # فیلد bits را برای بردار دودویی حالت نمونه با نوع مشخص‌شده نگه می‌دارد.
    bits::Vector{Int}
    # فیلد value را برای کران بالای هزینهٔ مقاوم نمونه با نوع مشخص‌شده نگه می‌دارد.
    value::Float64
    # فیلد scope را برای شناسهٔ مدل و دامنه‌ای که نتیجه برای آن معتبر است با نوع مشخص‌شده نگه می‌دارد.
    scope::String

    # سازندهٔ نمونهٔ بالایی را تعریف می‌کند که فقط نتیجهٔ دارای کران بالای معتبر را می‌پذیرد.
    function UpperSample(bits,result::CCGResult)
        # نقش کران یا تقریب آینده را کنترل می‌کند تا کران حل یک تقریب به‌جای گواه مسئلهٔ اصلی گزارش نشود.
        all(b->b==0||b==1,bits) && !result.infeasible && isfinite(result.upper) &&
            result.bound_role in (:exact,:upper) ||
            error(\"Certified, feasible finite upper result required; lower-envelope output is forbidden\")
        # بردار بیت و کران بالای گواه را با شناسهٔ دقیق هدف ذخیره می‌کند.
        new(Int.(bits),result.upper,result.scope)
    # تعریف تابع UpperSample را پایان می‌دهد.
    end
# تعریف ساختار UpperSample را پایان می‌دهد.
end

# دامنهٔ صریح حالت‌ها و یک کران بالای یکنواخت با شناسهٔ هزینهٔ مشترک را نگه می‌دارد.
struct DomainUpperCertificate
    # فیلد points را برای فهرست صریح حالت‌های دودویی دامنهٔ گواهی‌شده با نوع مشخص‌شده نگه می‌دارد.
    points::Vector{Vector{Int}}
    # فیلد bound را برای کران بالای یکنواخت هزینه روی دامنهٔ گواهی‌شده با نوع مشخص‌شده نگه می‌دارد.
    bound::Float64
    # فیلد scope را برای شناسهٔ مدل و دامنه‌ای که نتیجه برای آن معتبر است با نوع مشخص‌شده نگه می‌دارد.
    scope::String
# تعریف ساختار DomainUpperCertificate را پایان می‌دهد.
end

# گواه کران یکنواخت هزینه بر یک مجموعهٔ صریح از حالت‌های دودویی را محاسبه می‌کند.
function certify_upper_domain(points,evaluate; max_states=10000)
    # برای ساخت گواه دامنهٔ بالایی، وجود دست‌کم یک حالت صریح را الزامی می‌کند.
    isempty(points) && error(\"Empty upper domain\")
    # تعداد حالت‌های گواهی‌شونده را به بودجهٔ صریح کاربر محدود می‌کند.
    length(points)<=max_states || error(\"Upper-domain certification budget exceeded\")
    # طول کد، مجموعهٔ نقاط دیده‌شده و کران یکنواخت دامنه را مقداردهی می‌کند.
    n=length(first(points));seen=Set{String}();bound=-Inf;scope=nothing
    # هر حالت صریح دامنه را برای محاسبهٔ کران بالای گواه مستقل ارزیابی می‌کند.
    for b in points
        # طول مشترک و صفر و یک بودن همهٔ مؤلفه‌های حالت دامنه را کنترل می‌کند.
        length(b)==n && all(x->x==0||x==1,b) || error(\"Invalid domain state\")
        # یکتابودن کد حالت‌ها را کنترل می‌کند تا گواه دامنه و نمونه‌ها تکرار مبهم نداشته باشد.
        binary_key(b) in seen && error(\"Duplicate domain state\")
        # کلید حالت گواهی‌شونده را برای کنترل تکراری‌نبودن ثبت می‌کند.
        push!(seen,binary_key(b))
        # حل مقاوم دارای کران بالا را برای حالت دودویی جاری فراخوانی می‌کند.
        r=evaluate(b)
        # نقش کران یا تقریب آینده را کنترل می‌کند تا کران حل یک تقریب به‌جای گواه مسئلهٔ اصلی گزارش نشود.
        r isa CCGResult && isfinite(r.upper) && !r.infeasible && r.bound_role in (:exact,:upper) || error(\"Uncertified, lower-envelope, or infeasible domain state\")
        # شناسهٔ هزینهٔ نخستین نتیجه را شناسهٔ مشترک دامنه قرار می‌دهد.
        scope===nothing && (scope=r.scope)
        # همسانی شناسهٔ هدف هزینه را کنترل می‌کند تا گواه مدل، دوره یا نسخهٔ دیگری استفاده نشود.
        r.scope==scope || error(\"Upper-domain scopes differ\")
        # بیشترین کران بالای گواه حالت‌های دامنه را نگه می‌دارد.
        bound=max(bound,r.upper)
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # دامنهٔ صریح حالت‌ها، کران یکنواخت و شناسهٔ هزینه را به‌صورت گواه برمی‌گرداند.
    return DomainUpperCertificate([Int.(b) for b in points],bound,scope)
# تعریف تابع certify_upper_domain را پایان می‌دهد.
end

# تقریب بالایی را با نمونه‌های دارای گواه و قید عضویت در دامنهٔ گواهی‌شده به مدل اضافه می‌کند.
function attach_upper!(m,bits,alpha,samples::Vector{UpperSample},certificate::DomainUpperCertificate)
    # ساخت تقریب بالایی بدون نمونهٔ دارای گواه را رد می‌کند.
    isempty(samples) && error(\"Upper samples required\")
    # بعد بردار حالت دودویی مدل جاری را می‌گیرد.
    n=length(bits)
    # دودویی تعریف‌شدن خود متغیرهای حالت را پیش از افزودن تقریب بالایی کنترل می‌کند.
    all(is_binary,bits) || error(\"Eq61 requires the specified binary state representation\")
    # همسانی شناسهٔ هدف هزینه را کنترل می‌کند تا گواه مدل، دوره یا نسخهٔ دیگری استفاده نشود.
    all(length(s.bits)==n && s.scope==certificate.scope for s in samples) || error(\"Upper sample scope/layout mismatch\")
    # ترتیب و تعداد متغیرها را میان مدل‌های عددی، نمادین یا ستون ذخیره‌شده تطبیق می‌دهد.
    all(length(b)==n for b in certificate.points) || error(\"Upper domain layout mismatch\")
    # عضویت تک‌تک حالت‌های نمونه در فهرست صریح نقاط دارای گواه دامنه را کنترل می‌کند.
    all(any(b==s.bits for b in certificate.points) for s in samples) || error(\"Sample outside certified domain\")
    # وزن‌های ترکیب محدب حالت‌های دامنهٔ گواهی‌شده را ایجاد می‌کند.
    d=@variable(m,[1:length(certificate.points)],lower_bound=0.0)
    # مجموع وزن‌های عضویت در دامنه را یک می‌کند.
    @constraint(m,sum(d)==1)
    # روی تمام مؤلفه‌های بردار دودویی حلقه می‌زند.
    for j in 1:n
        # عضویت حالت دودویی در کدبوک گواهی‌شده را تحمیل می‌کند؛ حالت دودویی ترکیب محدب باید یکی از همان نقاط باشد.
        @constraint(m,bits[j]==sum(d[k]*certificate.points[k][j] for k in eachindex(d)))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # وزن‌های ترکیب محدب نمونه‌های دارای کران بالا را تعریف می‌کند.
    chi=@variable(m,[1:length(samples)],lower_bound=0.0)
    # بخش مثبت اختلاف نمونهٔ ترکیبی با حالت جاری را ایجاد می‌کند.
    dp=@variable(m,[1:n],lower_bound=0.0)
    # بخش منفی اختلاف نمونهٔ ترکیبی با حالت جاری را ایجاد می‌کند.
    dm=@variable(m,[1:n],lower_bound=0.0)
    # وزن‌های نمونه‌های بالایی را یک‌جمع می‌کند.
    @constraint(m,sum(chi)==1)
    # روی تمام مؤلفه‌های بردار دودویی حلقه می‌زند.
    for j in 1:n
        # اختلاف هر بیت حالت با ترکیب نمونه‌ها را به دو مؤلفهٔ نامنفی تجزیه می‌کند.
        @constraint(m,sum(chi[k]*samples[k].bits[j] for k in eachindex(chi))+dp[j]-dm[j]==bits[j])
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # A codebook certificate cannot be reused if its value or scope is invalid.
    isfinite(certificate.bound) || error(\"Nonfinite upper-codebook certificate\")
    all(b->length(b)==n && all(x->x in (0,1),b),certificate.points) ||
        error(\"Invalid binary upper-codebook state\")
    length(unique(binary_key.(certificate.points)))==length(certificate.points) ||
        error(\"Duplicate upper-codebook state\")
    certificate.bound+1e-8 >= maximum(s.value for s in samples) ||
        error(\"Upper-codebook bound is smaller than a certified sample\")
    # ضریب فاصله را از کران گواه دامنه استخراج می‌کند؛ عدد حدسی Big-M به آن نسبت داده نمی‌شود.
    penalty=max(0.0,certificate.bound-minimum(s.value for s in samples))
    # تقریب بالایی معتبر بر دامنهٔ تحمیل‌شده را به هزینهٔ آینده متصل می‌کند؛ اعتبار به حالت‌های خارج از دامنه تعمیم داده نمی‌شود.
    @constraint(m,alpha>=sum(chi[k]*samples[k].value for k in eachindex(chi))+penalty*sum(dp+dm))
    # ضریب مشتق‌شده و متغیرهای تقریب بالایی را برای بررسی برمی‌گرداند.
    return (;penalty,chi,dp,dm)
# تعریف تابع attach_upper! را پایان می‌دهد.
end
# نوع چندجمله‌ای عدم‌قطعیت را تعریف می‌کند؛ کلید تهی ثابت و کلیدهای دیگر اندیس بیت‌ها هستند.
const Poly15=Dict{Tuple{Vararg{Int}},Float64}
# ضریب غیرصفر را به تک‌جمله‌ای هم‌کلید اضافه و فرهنگ چندجمله‌ای را برمی‌گرداند.
addpoly!(p,k,v)=(v==0.0 || (p[k]=get(p,k,0.0)+v);p)

# عبارت نمادین را پس از تثبیت تصمیم‌های صحیح به ثابت و ضرایب متغیرهای پیوسته تجزیه می‌کند.
function split_parametric_expression(expr,unc_index,integer_values,continuous)
    # بخش ثابت و فرهنگ ضرایب چندجمله‌ای متغیرهای پیوسته را خالی آغاز می‌کند.
    offset=Poly15();coefs=Dict{VariableRef,Poly15}()

    # پردازش یک تک‌جمله‌ای برای جداکردن بیت‌های عدم‌قطعیت از متغیر پیوسته را تعریف می‌کند.
    function term(c,vars)
        # اندیس بیت‌ها، متغیرهای پیوسته و ضریب عددی تک‌جمله‌ای را آماده می‌کند.
        key=Int[];realvars=VariableRef[];factor=Float64(c)
        # عوامل تک‌جمله‌ای را برای تشخیص بیت عدم‌قطعیت، تصمیم صحیح ثابت یا متغیر پیوسته پیمایش می‌کند.
        for v in vars
            # اگر عامل یک بیت عدم‌قطعیت باشد، اندیس آن را در کلید تک‌جمله‌ای ثبت می‌کند.
            if haskey(unc_index,v);push!(key,unc_index[v])
            # اگر عامل تصمیم صحیح تثبیت‌شده باشد، مقدار ثابت آن را در ضریب ضرب می‌کند.
            elseif haskey(integer_values,v);factor*=integer_values[v]
            # عامل پیوستهٔ تصمیم را برای تشکیل ضریب LP جدا می‌کند.
            elseif v in continuous;push!(realvars,v)
            # وجود متغیر خارج از دسته‌بندی نمادین را خطا اعلام می‌کند.
            else;error(\"Unknown variable in symbolic recourse\")
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # کنترل می‌کند پس از تثبیت صحیح‌ها، هر تک‌جمله‌ای حداکثر یک متغیر پیوسته داشته باشد و پاسخ واقعاً LP بماند.
        length(realvars)<=1 || error(\"Recourse is nonlinear after fixing integer variables\")
        # کلید بیت‌ها را مرتب و تکرار بیت را حذف می‌کند، زیرا برای بیت دودویی رابطهٔ b²=b برقرار است.
        k=Tuple(sort(unique(key)))
        # شرط نبود متغیر پیوسته در تک‌جمله‌ای را بررسی می‌کند.
        if isempty(realvars)
            # تک‌جمله‌ای بدون متغیر پیوسته را به بخش ثابت اضافه می‌کند.
            addpoly!(offset,k,factor)
        # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
        else
            # تک‌جمله‌ای را به ضریب تنها متغیر پیوستهٔ موجود اضافه می‌کند.
            addpoly!(get!(coefs,only(realvars),Poly15()),k,factor)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
    # تعریف تابع term را پایان می‌دهد.
    end
    # شرط عددی‌بودن کامل عبارت را بررسی می‌کند.
    if expr isa Number
        # عبارت کاملاً عددی را به‌عنوان تک‌جمله‌ای ثابت پردازش می‌کند.
        term(expr,())
    # در غیر این صورت، شرط متغیر تنها بودن عبارت را بررسی می‌کند.
    elseif expr isa VariableRef
        # یک متغیر تنها را با ضریب یک پردازش می‌کند.
        term(1.0,(expr,))
    # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
    else
        # بخش افاین عبارت درجه‌دو را جدا می‌کند یا همان عبارت خطی را نگه می‌دارد.
        affine=expr isa GenericQuadExpr ? expr.aff : expr
        # جملهٔ ثابت بخش افاین را پردازش می‌کند.
        term(constant(affine),())
        # تمام جمله‌های خطی را با پردازشگر مشترک تجزیه می‌کند.
        for (c,v) in linear_terms(affine);term(c,(v,));end
        # شرط وجود جمله‌های درجه‌دو در عبارت را بررسی می‌کند.
        if expr isa GenericQuadExpr
            # تمام جمله‌های درجه‌دو را برای جداسازی عوامل ثابت، دودویی و پیوسته پردازش می‌کند.
            for (c,v,w) in quad_terms(expr);term(c,(v,w));end
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # چندجمله‌ای ثابت و ضرایب نمادین متغیرهای پیوسته را برمی‌گرداند.
    return offset,coefs
# تعریف تابع split_parametric_expression را پایان می‌دهد.
end

# حاصل‌ضرب یک یا دو بیت عدم‌قطعیت را به‌صورت دقیق بازنمایی می‌کند.
function binary_monomial!(m,key,z,and_cache)
    # برای تک‌جمله‌ای یک‌بیتی، همان بیت را بدون متغیر کمکی برمی‌گرداند.
    length(key)==1 && return z[only(key)]
    # پس از حالت تک‌بیتی، فقط تک‌جمله‌ای حاصل‌ضرب دو بیت را در این تبدیل می‌پذیرد.
    length(key)==2 || error(\"Only quadratic uncertainty terms supported\")
    # حاصل‌ضرب دو بیت را از حافظه می‌گیرد یا فقط یک‌بار می‌سازد.
    return get!(and_cache,key) do
        # یک متغیر دودویی کمکی برای بازنمایی دقیق رابطهٔ منطقی ایجاد می‌کند.
        b=@variable(m,binary=true)
        # حاصل‌ضرب دودویی را از بیت اول بزرگ‌تر نمی‌گذارد.
        @constraint(m,b<=z[key[1]])
        # حاصل‌ضرب دودویی را از بیت دوم بزرگ‌تر نمی‌گذارد.
        @constraint(m,b<=z[key[2]])
        # اگر هر دو بیت یک باشند، حاصل‌ضرب را یک می‌کند؛ سه قید با دودویی‌بودن AND دقیق می‌دهند.
        @constraint(m,b>=z[key[1]]+z[key[2]]-1)
        # بیت کمکی ساخته‌شده را به‌عنوان مقدار بلوک به حافظهٔ اشتراکی برمی‌گرداند.
        b
    # بلوک پردازش فایل یا ساخت یک‌بارهٔ مقدار حافظه را پایان می‌دهد.
    end
# تعریف تابع binary_monomial! را پایان می‌دهد.
end

# حاصل‌ضرب بیت در متغیر دوگان بدون کران‌سازی حدسی دوگان را با قیود شاخص می‌سازد.
function indicator_product!(m,z,lambda,cache)
    # کلید زوج بیت و متغیر دوگان را برای استفادهٔ دوباره از حاصل‌ضرب می‌سازد.
    key=(index(z).value,index(lambda).value)
    # متغیر حاصل‌ضرب بیت و دوگان را بازیابی می‌کند یا می‌سازد.
    return get!(cache,key) do
        # Product w = z * lambda. When mathematically certified finite dual
        # bounds exist (Farkas L1 normalization), use the EXACT four-row
        # binary/continuous convex hull rather than indicator constraints.
        # This changes neither physical data nor the uncertainty set.
        w=@variable(m)
        lo=has_lower_bound(lambda) ? lower_bound(lambda) : -Inf
        hi=has_upper_bound(lambda) ? upper_bound(lambda) : Inf
        if isfinite(lo) && isfinite(hi)
            lo<=hi || error(\"Inconsistent certified dual bounds\")
            @constraint(m,w>=lo*z)
            @constraint(m,w<=hi*z)
            @constraint(m,w>=lambda-hi*(1-z))
            @constraint(m,w<=lambda-lo*(1-z))
            return w
        end
        # Unbounded optimality duals must retain exact indicators; never
        # introduce a guessed big-M for the optimality master.
        # بیت مکمل را برای فعال‌سازی قیود هنگام صفر بودن بیت اصلی بازیابی یا ایجاد می‌کند.
        complement=get!(cache,(:complement,index(z).value)) do
            # یک متغیر دودویی کمکی برای بازنمایی دقیق رابطهٔ منطقی ایجاد می‌کند.
            b=@variable(m,binary=true)
            # بیت کمکی را دقیقاً مکمل بیت اصلی قرار می‌دهد.
            @constraint(m,b+z==1)
            # بیت کمکی ساخته‌شده را به‌عنوان مقدار بلوک به حافظهٔ اشتراکی برمی‌گرداند.
            b
        # بلوک پردازش فایل یا ساخت یک‌بارهٔ مقدار حافظه را پایان می‌دهد.
        end
        # وقتی بیت اصلی یک است، نیمهٔ اول برابری حاصل‌ضرب و دوگان را فعال می‌کند.
        @constraint(m,z --> {w-lambda<=0})
        # وقتی بیت اصلی یک است، نیمهٔ دوم برابری حاصل‌ضرب و دوگان را فعال می‌کند.
        @constraint(m,z --> {lambda-w<=0})
        # وقتی بیت اصلی صفر است، حد بالای حاصل‌ضرب را صفر می‌کند.
        @constraint(m,complement --> {w<=0})
        # وقتی بیت اصلی صفر است، حد پایین حاصل‌ضرب را صفر می‌کند؛ چهار شاخص رابطهٔ w=zλ را می‌دهند.
        @constraint(m,complement --> {-w<=0})
        # متغیر حاصل‌ضرب دقیق بیت و دوگان را به‌عنوان مقدار بلوک برمی‌گرداند.
        w
    # بلوک پردازش فایل یا ساخت یک‌بارهٔ مقدار حافظه را پایان می‌دهد.
    end
# تعریف تابع indicator_product! را پایان می‌دهد.
end

# چندجمله‌ای دودویی عدم‌قطعیت را به عبارت خطی همراه متغیرهای AND تبدیل می‌کند.
function polynomial_affine!(m,p,z,and_cache)
    # عبارت خطی را با ضریب ثابت چندجمله‌ای آغاز می‌کند.
    e=AffExpr(get(p,(),0.0))
    # کلید تک‌جمله‌ای دودویی و ضریب آن را در چندجمله‌ای پردازش می‌کند.
    for (key,c) in p
        # جمله‌های غیرثابت و غیرصفر را با بازنمایی دقیق تک‌جمله‌ای دودویی به عبارت اضافه می‌کند.
        isempty(key) || c==0.0 || add_to_expression!(e,c,binary_monomial!(m,key,z,and_cache))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # عبارت افاین ساخته‌شده از چندجمله‌ای دودویی و متغیرهای کمکی را برمی‌گرداند.
    return e
# تعریف تابع polynomial_affine! را پایان می‌دهد.
end

# حاصل‌ضرب چندجمله‌ای دودویی در متغیر دوگان را با قیود شاخص بازنمایی می‌کند.
function polynomial_times_dual!(m,p,lambda,z,and_cache,product_cache)
    # عبارت خطی حاصل‌ضرب چندجمله‌ای و دوگان را از صفر آغاز می‌کند.
    e=AffExpr(0.0)
    # کلید تک‌جمله‌ای دودویی و ضریب آن را در چندجمله‌ای پردازش می‌کند.
    for (key,c) in p
        # جملهٔ با ضریب صفر را برای کوچک‌ماندن مدل کنار می‌گذارد.
        c==0.0 && continue
        # شرط ثابت‌بودن جمله نسبت به بیت‌های عدم‌قطعیت را بررسی می‌کند.
        if isempty(key)
            # جملهٔ ثابت چندجمله‌ای را مستقیماً در متغیر دوگان ضرب می‌کند.
            add_to_expression!(e,c,lambda)
        # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
        else
            # بیت یا AND متناظر با تک‌جمله‌ای عدم‌قطعیت را می‌گیرد.
            b=binary_monomial!(m,key,z,and_cache)
            # ضریب در حاصل‌ضرب دقیق تک‌جمله‌ای دودویی و متغیر دوگان را اضافه می‌کند.
            add_to_expression!(e,c,indicator_product!(m,b,lambda,product_cache))
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # عبارت افاین ساخته‌شده از چندجمله‌ای دودویی و متغیرهای کمکی را برمی‌گرداند.
    return e
# تعریف تابع polynomial_times_dual! را پایان می‌دهد.
end

# دوگان LP مربوط به یک الگوی صحیح تثبیت‌شده را در مستر نمادین می‌سازد.
function add_symbolic_dual_column!(master,z,pattern,uncertainty_factory,symbolic_builder;
        # حالت ساخت پرتو و حافظه‌های مشترک AND و حاصل‌ضرب دوگان را به‌صورت ورودی اختیاری تعریف می‌کند.
        ray=false,and_cache=Dict(),product_cache=Dict())
    # مدل موقت بدون حل‌کننده را برای استخراج ساختار نمادین مسئلهٔ اولیه ایجاد می‌کند.
    pm=Model()
    # متغیرهای عدم‌قطعیت و سناریوی نمادین را در مدل موقت می‌سازد.
    uz,unc,_=uncertainty_factory(pm)
    # ترتیب و تعداد متغیرها را میان مدل‌های عددی، نمادین یا ستون ذخیره‌شده تطبیق می‌دهد.
    length(uz)==length(z) || error(\"Uncertainty layout changed between models\")
    # قیود صرفاً مربوط به دامنهٔ عدم‌قطعیت را پیش از افزودن مدل فیزیکی ثبت می‌کند.
    snapshot=Set(all_constraints(pm;include_variable_in_set_constraints=true))
    # مدل فیزیکی و تقریب آینده را با ضرایب نمادین عدم‌قطعیت به مدل موقت اضافه می‌کند.
    symbolic_builder(pm,unc)
    # مجموعهٔ بیت‌های عدم‌قطعیت را برای جداسازی از تصمیم‌های پاسخ تشکیل می‌دهد.
    uset=Set(uz)
    # متغیرهای تصمیم پاسخ را با حذف بیت‌های عدم‌قطعیت استخراج می‌کند.
    primal=filter(v->!(v in uset),all_variables(pm))
    # ترتیب محلی متغیرهای پاسخ را مطابق مدل عددی ثبت می‌کند.
    ordinal=Dict(v=>i for (i,v) in enumerate(primal))
    # تمام متغیرهای صحیح پاسخ را برای جایگذاری الگوی ستون انتخاب می‌کند.
    iv=filter(v->is_binary(v)||is_integer(v),primal)
    # ترتیب و تعداد متغیرها را میان مدل‌های عددی، نمادین یا ستون ذخیره‌شده تطبیق می‌دهد.
    [ordinal[v] for v in iv]==pattern.indices || error(\"Symbolic/oracle integer layouts differ\")
    # هر تصمیم صحیح نمادین را به مقدار ثابت آن در ستون نگاشت می‌کند.
    integers=Dict(v=>k for (v,k) in zip(iv,pattern.values))
    # پس از جایگذاری همهٔ تصمیم‌های صحیح، مجموعهٔ متغیرهای پیوستهٔ LP را تشکیل می‌دهد.
    continuous=Set(filter(v->!haskey(integers,v),primal))
    # شمارهٔ بیت‌های عدم‌قطعیت مدل موقت را ثبت می‌کند.
    unc_index=Dict(v=>i for (i,v) in enumerate(uz))
    # تابع هدف را به ثابت نمادین و ضرایب هزینهٔ متغیرهای پیوسته تجزیه می‌کند.
    c0,c=split_parametric_expression(objective_function(pm),unc_index,integers,continuous)
    # سمت چپ تساوی‌های ایستایی دوگان را برای هر متغیر پیوسته خالی آغاز می‌کند.
    stationarity=Dict(v=>AffExpr(0.0) for v in continuous)
    # روی تمام متغیرهای پیوستهٔ LP پس از تثبیت صحیح‌ها حلقه می‌زند.
    for v in continuous
        # چندجمله‌ای ضریب هزینهٔ متغیر پیوستهٔ جاری را می‌گیرد.
        coef=get(c,v,Poly15())
        # مستقل‌بودن ضرایب هزینهٔ متغیرهای پیوسته از عدم‌قطعیت را برای این تبدیل نمادین کنترل می‌کند.
        any(!isempty(k)&&a!=0 for (k,a) in coef) && error(\"Uncertain continuous objective unsupported\")
        # ضریب ثابت هزینهٔ متغیر پیوسته را استخراج می‌کند.
        a=get(coef,(),0.0)
        # شرط ساخت دوگان هزینه به‌جای پرتو فارکاس را بررسی می‌کند.
        if !ray
            # شرط کافی امکان‌پذیری دوگان را از علامت هزینه و وجود حد مناسب یا تثبیت متغیر کنترل می‌کند.
            (a==0 || is_fixed(v) || (a>0&&has_lower_bound(v)&&isfinite(lower_bound(v))) || (a<0&&has_upper_bound(v)&&isfinite(upper_bound(v)))) ||
                # با پیام مشخص‌شده توقف می‌کند تا وضعیت فاقد گواه یا ساختار پشتیبانی‌نشده به نتیجهٔ معتبر تبدیل نشود.
                error(\"Variable bounds do not certify dual feasibility; use reference backend\")
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # هدف دوگان عادی را با ثابت هزینه و هدف پرتوی فارکاس را با صفر آغاز می‌کند.
    dual_obj=ray ? AffExpr(0.0) : polynomial_affine!(master,c0,z,and_cache)
    # متغیرهای کمکی نرم L1 پرتو فارکاس را خالی ایجاد می‌کند.
    normvars=VariableRef[]
    # همهٔ قیود اولیه و حدود متغیرها را برای استخراج کامل دوگان LP بررسی می‌کند.
    for con in all_constraints(pm;include_variable_in_set_constraints=true)
        # قیود دامنهٔ عدم‌قطعیت را از دوگان LP پاسخ کنار می‌گذارد؛ آن‌ها در مستر مستقل حضور دارند.
        con in snapshot && continue
        # تابع و مجموعهٔ قید اولیه را برای استخراج دوگان می‌خواند.
        obj=constraint_object(con)
        # قید نوع دودویی را پس از جایگذاری مقدار صحیح وارد دوگان LP نمی‌کند.
        obj.set isa MOI.ZeroOne && continue
        # قید نوع صحیح را پس از تثبیت الگو وارد دوگان LP نمی‌کند.
        obj.set isa MOI.Integer && continue
        # قید پاسخ را به ثابت و ضرایب متغیرهای پیوسته با وابستگی به عدم‌قطعیت تجزیه می‌کند.
        off,A=split_parametric_expression(obj.func,unc_index,integers,continuous)
        # نوع مجموعهٔ قید اولیه را تشخیص می‌دهد تا تساوی یا نامساوی متناظر دوگان ساخته شود.
        pieces=if obj.set isa MOI.EqualTo
            # قید برابری را با یک ضریب دوگان آزاد بازنمایی می‌کند.
            ((:eq,obj.set.value),)
        # شرط «obj.set isa MOI.LessThan» را برای انتخاب شاخهٔ مناسب بررسی می‌کند.
        elseif obj.set isa MOI.LessThan
            # قید کمترمساوی را برای ضریب دوگان نامثبت ثبت می‌کند.
            ((:le,obj.set.upper),)
        # شرط «obj.set isa MOI.GreaterThan» را برای انتخاب شاخهٔ مناسب بررسی می‌کند.
        elseif obj.set isa MOI.GreaterThan
            # قید بیشترمساوی را برای ضریب دوگان نامنفی ثبت می‌کند.
            ((:ge,obj.set.lower),)
        # شرط «obj.set isa MOI.Interval» را برای انتخاب شاخهٔ مناسب بررسی می‌کند.
        elseif obj.set isa MOI.Interval
            # قید بازه‌ای را به دو نامساوی با دو ضریب دوگان مستقل می‌شکند.
            ((:ge,obj.set.lower),(:le,obj.set.upper))
        # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
        else
            # با پیام مشخص‌شده توقف می‌کند تا وضعیت فاقد گواه یا ساختار پشتیبانی‌نشده به نتیجهٔ معتبر تبدیل نشود.
            error(\"Unsupported symbolic LP constraint \$(typeof(obj.set))\")
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # هر تساوی یا نیمهٔ نامساوی قید را با علامت و حد سمت راست آن به دوگان تبدیل می‌کند.
        for (sense,rhs) in pieces
            # متغیر دوگان قید را ابتدا آزاد تعریف می‌کند.
            lambda=@variable(master)
            # برای قید کمترمساوی در مسئلهٔ کمینه‌سازی، دوگان را نامثبت می‌کند.
            sense==:le && set_upper_bound(lambda,0.0)
            # برای قید بیشترمساوی در مسئلهٔ کمینه‌سازی، دوگان را نامنفی می‌کند.
            sense==:ge && set_lower_bound(lambda,0.0)
            # شرط ساخت پرتو امکان‌پذیری فارکاس را بررسی می‌کند.
            if ray
                # The existing sum(abs(lambda)) <= 1 Farkas normalization
                # rigorously implies -1 <= lambda <= 1 for EVERY multiplier.
                # Explicit bounds enable the exact McCormick/Fortet product
                # hull above. These are NOT empirical big-M coefficients.
                if sense==:eq
                    set_lower_bound(lambda,-1.0)
                    set_upper_bound(lambda,1.0)
                elseif sense==:le
                    set_lower_bound(lambda,-1.0) # upper bound already 0
                elseif sense==:ge
                    set_upper_bound(lambda,1.0) # lower bound already 0
                else
                    error(\"Unknown Farkas multiplier sign\")
                end
                # قدر مطلق کمکی دوگان پرتو را برای نرمال‌سازی فارکاس تعریف می‌کند؛ این کران از مقیاس پرتو می‌آید.
                av=@variable(master,lower_bound=0.0,upper_bound=1.0)
                # نیمهٔ مثبت قدرمطلق ضریب پرتو فارکاس را اعمال می‌کند.
                @constraint(master,av>=lambda)
                # نیمهٔ منفی قدرمطلق ضریب پرتو فارکاس را اعمال می‌کند.
                @constraint(master,av>=-lambda)
                # متغیر قدرمطلق را برای قید مجموع نرم پرتو ثبت می‌کند.
                push!(normvars,av)
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
            # ضرایب نمادین متغیرهای پیوستهٔ قید را برای تکمیل معادلات ایستایی پیمایش می‌کند.
            for (v,coeffs) in A
                # سهم ضریب قید ضربدر دوگان را به معادلهٔ ایستایی متغیر پیوسته اضافه می‌کند.
                stationarity[v]+=polynomial_times_dual!(master,coeffs,lambda,z,and_cache,product_cache)
            # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
            end
            # منفی ثابت نمادین قید را برای ساخت سمت راست مؤثر دوگان تشکیل می‌دهد.
            rpoly=Poly15(k=>-a for (k,a) in off)
            # حد قید را به ثابت سمت راست مؤثر اضافه می‌کند.
            addpoly!(rpoly,(),rhs)
            # سهم سمت راست مؤثر ضربدر دوگان را به هدف دوگان اضافه می‌کند.
            dual_obj+=polynomial_times_dual!(master,rpoly,lambda,z,and_cache,product_cache)
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # روی تمام متغیرهای پیوستهٔ LP پس از تثبیت صحیح‌ها حلقه می‌زند.
    for v in continuous
        # ایستایی دوگان عادی را برابر هزینه و ایستایی پرتو فارکاس را برابر صفر می‌کند.
        @constraint(master,stationarity[v]==(ray ? 0.0 : get(get(c,v,Poly15()),(),0.0)))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # نرم L1 پرتو فارکاس را حداکثر یک می‌کند؛ این نرمال‌سازی همگن است و Big-M هزینه نیست.
    ray && !isempty(normvars) && @constraint(master,sum(normvars)<=1.0)
    # عبارت هدف دوگان ستون یا پرتو امکان‌پذیری را برمی‌گرداند.
    return dual_obj
# تعریف تابع add_symbolic_dual_column! را پایان می‌دهد.
end

# مستر بیشینه‌سازی عدم‌قطعیت را در حالت امکان‌پذیری فارکاس یا حالت بهینگی می‌سازد.
function symbolic_master(columns,uncertainty_factory,symbolic_builder,optimizer;
        # حالت امکان‌پذیری یا بهینگی و بودجهٔ زمان مستر را تعیین می‌کند.
        ray=false,seconds=600.0)
    # مدل مستر را با حل‌کنندهٔ دارای پشتیبانی قیود شاخص، مانند SCIP، ایجاد می‌کند.
    m=Model(optimizer)
    # خروجی حل‌کننده را ساکت و مهلت حل مدل را تنظیم می‌کند.
    set_silent(m);set_time_limit_sec(m,Float64(seconds))
    # کل دامنهٔ عدم‌قطعیت نمادین و تابع استخراج سناریو را در مستر می‌سازد.
    z,unc,extract=uncertainty_factory(m)
    # متغیر آزاد مقدار هدف مستر بیشینه‌سازی را ایجاد می‌کند.
    eta=@variable(m)
    # در مستر امکان‌پذیری، مقدار کمینهٔ گواه فارکاس را صفر قرار می‌دهد.
    ray && set_lower_bound(eta,0.0)
    # حافظهٔ مشترک متغیرهای AND و حاصل‌ضرب بیت در دوگان را ایجاد می‌کند.
    and_cache=Dict();product_cache=Dict()
    # روی همهٔ ستون‌های صحیح موجود حلقه می‌زند.
    for p in columns
        # دوگان نمادین LP ستون جاری را با همهٔ وابستگی‌های ماتریس به عدم‌قطعیت می‌سازد.
        dual=add_symbolic_dual_column!(m,z,p,uncertainty_factory,symbolic_builder;
            # نوع پرتو و حافظه‌های مشترک بازنمایی دودویی را به سازندهٔ ستون دوگان می‌فرستد.
            ray,and_cache,product_cache)
        # مقدار مستر را با هزینهٔ دوگان هر الگوی صحیح محدود می‌کند.
        @constraint(m,eta<=dual)
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # سناریویی را جست‌وجو می‌کند که کمترین هزینهٔ ستون‌های موجود را بیشینه کند.
    @objective(m,Max,eta)
    # مدل مستر و تابع استخراج سناریوی جواب آن را برمی‌گرداند.
    return m,extract
# تعریف تابع symbolic_master را پایان می‌دهد.
end

# C&CG با مستر نمادین تمام بیت‌های عدم‌قطعیت و اوراکل داخلی MILP را تعریف می‌کند.
function solve_native_ccg(builder,uncertainty_factory,symbolic_builder,seed;
        # حل‌کنندهٔ مستر، شناسهٔ هدف، سقف تکرار، بودجهٔ زمان و تلرانس شکاف را دریافت می‌کند.
        optimizer,scope,max_iters=100,seconds=600.0,rtol=0.001,
        # The Farkas master is now an indicator-free MILP. HiGHS can solve
        # it directly; the optimality master retains SCIP's native indicators.
        farkas_optimizer=HiGHS.Optimizer,
        # آستانهٔ تشخیص گواه مثبت فارکاس و نقش تقریب هزینهٔ آینده را تعیین می‌کند.
        feasibility_tol=1e-8,bound_role=:exact)
    # تعداد تکرار و زمان مثبت و تلرانس نسبی بین صفر و یک را برای C&CG نمادین کنترل می‌کند.
    max_iters>0 && seconds>0 && 0<=rtol<1 || error(\"Invalid C&CG settings\")
    # نقش کران یا تقریب آینده را کنترل می‌کند تا کران حل یک تقریب به‌جای گواه مسئلهٔ اصلی گزارش نشود.
    bound_role in (:exact,:lower,:upper) || error(\"Invalid envelope role\")
    # ستون‌ها، کلیدهای دیده‌شده و تاریخچهٔ C&CG نمادین را خالی آغاز می‌کند.
    columns=IntegerPattern[];seen=Set{String}();history=NamedTuple[]
    # کران‌ها و سناریوی آغازین و شاهد را مقداردهی می‌کند.
    lower=-Inf;upper=Inf;candidate=seed;best=seed
    # روی تکرارهای مجاز الگوریتم تا سقف تعیین‌شده حلقه می‌زند.
    for iteration in 1:max_iters
        # MILP کامل پاسخ را در سناریوی جاری می‌سازد، مهلت حل می‌دهد و حل می‌کند.
        inner=ensure_solver_column!(builder(candidate));set_time_limit_sec(inner,Float64(seconds));solve_tracked!(inner;context=\"ccg_inner_stage_scenario\")
        # کران پایین داخلی و هزینهٔ جواب قابل قبول را با کنترل وضعیت حل استخراج می‌کند.
        row=min_bounds(inner)
        # اگر پاسخ MILP در یک سناریوی مجاز ناممکن باشد، عدم امکان مقاوم را گزارش می‌کند.
        if row.status==MOI.INFEASIBLE
            # An upper-envelope codebook can exclude otherwise feasible
            # physical responses. Do not promote its INFEASIBLE status to
            # robust infeasibility of the unrestricted physical problem.
            if bound_role==:upper
                return CCGResult(lower,Inf,false,false,candidate,columns,history,
                    scope,:upper_codebook_or_physical_infeasible,bound_role)
            end
            return CCGResult(Inf,Inf,false,true,candidate,columns,history,
                scope,:robust_infeasible,bound_role)
        end
        # کران پایین مقاوم را با گواه بهتر در یک سناریوی مجاز به‌روز می‌کند.
        if row.lower>lower;lower=row.lower;best=candidate;end
        # در نبود جواب قابل قبول داخلی، کران‌های موجود را بدون اعلام همگرایی برمی‌گرداند.
        row.feasible || return CCGResult(lower,upper,false,false,best,columns,history,scope,:inner_no_incumbent,bound_role)
        # همهٔ تصمیم‌های صحیح جواب داخلی را به‌عنوان ستون بالقوه استخراج می‌کند.
        p=integer_pattern(inner)
        # شرط جدیدبودن ستون صحیح اوراکل داخلی را بررسی می‌کند.
        if !(pattern_key(p) in seen)
            # کلید و مقادیر ستون صحیح جدید را ذخیره می‌کند.
            push!(seen,pattern_key(p));push!(columns,p)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # مستر فارکاس را برای پیدا کردن سناریوی ناسازگار با همهٔ ستون‌های فعلی می‌سازد.
        fm,extract_f=symbolic_master(columns,uncertainty_factory,symbolic_builder,farkas_optimizer;ray=true,seconds)
        # No indicator is allowed in the Farkas master after exact L1-bounded
        # linearization; fail early rather than silently accepting drift.
        for (_,set_type) in list_of_constraint_types(fm)
            set_type <: MOI.Indicator && error(\"Farkas master still contains indicators: \$set_type\")
        end
        # مستر امکان‌پذیری فارکاس را حل می‌کند.
        solve_tracked!(fm;context=\"ccg_farkas_linearized_master\")
        # وضعیت توقف حل مستر امکان‌پذیری را می‌خواند.
        fstatus=termination_status(fm)
        # ناممکن‌شدن خود مستر فارکاس را نشانهٔ ساخت ناسازگار مدل می‌گیرد؛ پرتو صفر باید مجاز باشد.
        fstatus==MOI.INFEASIBLE && error(\"Farkas master infeasible: invalid symbolic construction\")
        # وجود جواب قابل قبول برای مستر امکان‌پذیری را کنترل می‌کند.
        ffeasible=has_values(fm)&&primal_status(fm)==MOI.FEASIBLE_POINT
        # شرط وجود گواه مثبت فارکاس برای ناسازگاری همهٔ ستون‌ها در یک سناریو را بررسی می‌کند.
        # بدون کران گواه، از مستر امکان‌پذیری به مستر بهینگی عبور نمی‌کنیم.
        fbound=try objective_bound(fm) catch; Inf end
        fvalue=ffeasible ? objective_value(fm) : NaN
        gate=farkas_gate(fstatus,ffeasible,fvalue,fbound;tol=feasibility_tol)
        if gate==:unresolved
            push!(history,(;iteration,lower,upper,master_complete=false,
                columns=length(columns),phase=:feasibility_unresolved,
                feasibility_bound=fbound,feasibility_status=string(fstatus),
                feasibility_incumbent=fvalue))
            return CCGResult(lower,upper,false,false,best,columns,history,scope,
                :feasibility_uncertified,bound_role)
        end
        if gate==:witness
            # سناریوی دارای گواه مثبت فارکاس را به اوراکل داخلی بعدی می‌فرستد.
            candidate=extract_f()
            # پیشرفت فاز امکان‌پذیری و کران‌های موجود را ثبت می‌کند؛ مستر بهینگی این تکرار هنوز حل نشده است.
            push!(history,(;iteration,lower,upper,master_complete=false,columns=length(columns),phase=:feasibility))
            # باقی دستورهای این تکرار را رد و تکرار بعدی حلقه را آغاز می‌کند.
            continue
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # مستر بهینگی را با دوگان LP همهٔ ستون‌های فعلی و کل دامنهٔ نمادین می‌سازد.
        master,extract=symbolic_master(columns,uncertainty_factory,symbolic_builder,optimizer;seconds)
        # مستر بهینگی بیشینه‌سازی را روی تمام مختصات فعال عدم‌قطعیت حل می‌کند.
        solve_tracked!(master;context=\"ccg_optimality_indicator_master\")
        # وضعیت توقف مستر بهینگی را می‌خواند.
        st=termination_status(master)
        # وضعیت‌های ناممکن، نامحدود یا مبهم مستر را برای بازگشت نتیجهٔ حل‌نشده تشخیص می‌دهد.
        st in (MOI.INFEASIBLE,MOI.DUAL_INFEASIBLE,MOI.INFEASIBLE_OR_UNBOUNDED) &&
            # کران‌ها، شاهد، تاریخچه و علت توقف C&CG را با همان نقش و دامنهٔ ثبت‌شده برمی‌گرداند.
            return CCGResult(lower,upper,false,false,best,columns,history,scope,:unresolved_master_feasibility,bound_role)
        # کران گواه بیشینه‌سازی مستر را به‌عنوان کران بالا می‌خواند؛ مقدار جواب مستر جای آن استفاده نمی‌شود.
        ub=try objective_bound(master) catch; Inf end
        # کران بالای عددی نامعتبر را به مثبت بی‌نهایت تبدیل می‌کند.
        isnan(ub) && (ub=Inf)
        # بهترین کران بالای مقاوم برای مدل با نقش ثبت‌شده را نگه می‌دارد.
        upper=min(upper,ub)
        # شرط وجود هم‌زمان کران پایین و بالای متناهی مقاوم را بررسی می‌کند.
        if isfinite(lower)&&isfinite(upper)
            # ترتیب صحیح کران پایین و بالا را با تلرانس عددی کنترل می‌کند و ناسازگاری را خطا می‌گیرد.
            lower<=upper+1e-6*max(1.0,abs(lower),abs(upper)) || error(\"Native C&CG bounds cross\")
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
        # کران‌های گواه و بهینه‌بودن حل مستر را در سطر تاریخچه ثبت می‌کند.
        push!(history,(;iteration,lower,upper,master_complete=st==MOI.OPTIMAL,
            # تعداد ستون‌ها و برچسب فاز بهینگی را به سطر تاریخچه اضافه می‌کند.
            columns=length(columns),phase=:optimality))
        # فقط با بسته‌شدن شکاف دو کران معتبر، نتیجه را همگرا با علت gap اعلام می‌کند.
        gap_closed(lower,upper,rtol) && return CCGResult(lower,upper,true,false,best,columns,history,scope,:gap,bound_role)
        # وجود جواب قابل قبول مستر را پیش از استخراج سناریوی تکرار بعد کنترل می‌کند.
        has_values(master)&&primal_status(master)==MOI.FEASIBLE_POINT ||
            # کران‌ها، شاهد، تاریخچه و علت توقف C&CG را با همان نقش و دامنهٔ ثبت‌شده برمی‌گرداند.
            return CCGResult(lower,upper,false,false,best,columns,history,scope,:master_no_incumbent,bound_role)
        # سناریوی صحیح جواب مستر بهینگی را برای تکرار بعد استخراج می‌کند.
        candidate=extract()
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # کران‌ها، شاهد، تاریخچه و علت توقف C&CG را با همان نقش و دامنهٔ ثبت‌شده برمی‌گرداند.
    return CCGResult(lower,upper,false,false,best,columns,history,scope,:iteration_limit,bound_role)
# تعریف تابع solve_native_ccg را پایان می‌دهد.
end
# گواه فضای کامل: ساخت آن نیازمند ارزیابی واقعی تمام کدهای دودویی است.
# این مسیر برای مدل‌های کوچک قابل اجراست؛ بودجهٔ ناکافی هرگز به گواه ساختگی تبدیل نمی‌شود.
struct FullBinaryUpperCertificate
    dimension::Int
    bound::Float64
    scope::String
    cardinality::BigInt
end
function certify_full_binary_upper(n::Int,evaluate;max_states=10000)
    n>=0 || error(\"Negative binary dimension\")
    total=big(2)^n
    total<=max_states || error(\"Full binary-domain proof exceeds explicit state budget\")
    bound=-Inf;scope=nothing
    for code in big(0):total-1
        bits=[Int((code>>(j-1))&1) for j in 1:n]
        r=evaluate(bits)
        r isa CCGResult && r.bound_role in (:exact,:upper) && !r.infeasible && isfinite(r.upper) ||
            error(\"Full domain has an uncertified or infeasible state; no finite global slope certified\")
        scope===nothing && (scope=r.scope)
        scope==r.scope || error(\"Full-domain target mismatch\")
        bound=max(bound,r.upper)
    end
    return FullBinaryUpperCertificate(n,bound,scope,total)
end
# بدون قید عضویت کدبوک، گسترش معادلهٔ ۶۱ تنها با گواه پوشش کامل مجاز است.
function attach_upper!(m,bits,alpha,samples::Vector{UpperSample},cert::FullBinaryUpperCertificate)
    n=length(bits)
    n==cert.dimension && all(is_binary,bits) || error(\"Full upper certificate layout mismatch\")
    cert.cardinality==big(2)^n && isfinite(cert.bound) || error(\"Incomplete global domain certificate\")
    !isempty(samples) && all(length(s.bits)==n && s.scope==cert.scope for s in samples) ||
        error(\"Invalid full-domain upper samples\")
    # Reject internally inconsistent upper-bound metadata before constructing Eq. (61).
    cert.bound+1e-8>=maximum(s.value for s in samples) ||
        error(\"Full-domain upper bound below certified sample\")
    chi=@variable(m,[1:length(samples)],lower_bound=0.)
    dp=@variable(m,[1:n],lower_bound=0.);dm=@variable(m,[1:n],lower_bound=0.)
    @constraint(m,sum(chi)==1)
    for j in 1:n
        @constraint(m,sum(chi[k]*samples[k].bits[j] for k in eachindex(chi))+dp[j]-dm[j]==bits[j])
    end
    # با تغییر مجموعهٔ نمونه‌ها شیب دوباره از گواه B محاسبه می‌شود؛ شیب حدسی مقاله نیست.
    penalty=max(0.,cert.bound-minimum(s.value for s in samples))
    @constraint(m,alpha>=sum(chi[k]*samples[k].value for k in eachindex(chi))+penalty*sum(dp+dm))
    return (;penalty,chi,dp,dm)
end

# پایان ماژول هستهٔ ریاضی.
end
# توابع هش SHA را برای امضای مدل و کنترل هویت گواه‌ها بارگذاری می‌کند.
using SHA
using TOML
# اثر انگشت منبع تنها یک‌بار هنگام بارگذاری محاسبه می‌شود.
const MODEL_SOURCE_HASH = bytes2hex(sha256(read(@__FILE__)))
# رابط SCIP را برای مستر MILP دارای قیود شاخص بومی بارگذاری می‌کند.

# شناسهٔ هدف هزینه را از دوره، شبکه، فرض‌های فیزیکی و امضای فایل منبع می‌سازد.
function physical_cost_scope(t,grids;domain=full_uncertainty_domain(t),capacity_mode=CHARGING_CAPACITY_MODE,
        initial_station_state::AbstractVector{<:Real})
    description=repr((t,[(k,grids[k].lo,grids[k].step,grids[k].last) for k in (\"Cc\",\"Ce\",\"Cv\")],
        capacity_mode,g7_scope_fields(),Tuple(Int.(initial_station_state)),
        disc_step_kw,CHARGING_ASSIGNMENT_MODE,LINE1_MODE,CANDIDATE_MODE,collect(A_set),
        domain.scope,domain.cardinality,MODEL_SOURCE_HASH))
    return \"REVCS finite-resolution cost-to-go / \"*bytes2hex(sha256(description))
end

# دامنهٔ کامل تصویر فیزیکی روابط دودویی عدم‌قطعیت را به‌صورت تنبل می‌سازد.
function full_uncertainty_domain(t::Int)
    # شمارهٔ دوره را پیش از ساخت دامنه با مجموعهٔ دوره‌های مدل تطبیق می‌دهد.
    t in T_set || error(\"Invalid planning stage\")
    # شرط دورهٔ نخست و قطعی برنامه‌ریزی را بررسی می‌کند.
    if t==1
        # سناریوی قطعی ریشه را با رشد پیش‌بینی‌شدهٔ تقاضای دورهٔ اول آغاز می‌کند.
        root=Dict{String,Any}(\"name\"=>\"deterministic root\",\"theta_t\"=>theta_fc[1],
            # ورودی‌های «zeta_t، xi_wt» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
            \"zeta_t\"=>zeta_fc[1],\"xi_wt\"=>repeat(wt_profile',num_wt,1),
            # ورودی‌های «zeta_pv» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
            \"zeta_pv\"=>repeat(pv_profile',num_pv_pdn,1),
            # ورودی‌های «zeta_station_pv» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
            \"zeta_station_pv\"=>repeat(pv_profile',num_roads,1))
        # تعریف دامنهٔ تکرارپذیر را با تعداد دقیق و شناسهٔ آن برمی‌گرداند.
        return REVCSCertifiedCore.UncertaintyDomain(()->(root,),1,\"full Phi_1, deterministic\")
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # فهرست مختصات فعال عدم‌قطعیت را شامل نوع، شمارهٔ واحد یا محل و ساعت خالی ایجاد می‌کند.
    coords=Tuple{Symbol,Int,Int}[]
    # اگر خطای رشد تقاضا غیرصفر باشد، یک مختصهٔ مستقل رشد تقاضا اضافه می‌کند.
    theta_err[t]>0 && push!(coords,(:theta,0,0))
    # اگر خطای رشد ظرفیت تجدیدپذیر غیرصفر باشد، یک مختصهٔ مستقل رشد ظرفیت اضافه می‌کند.
    zeta_err[t]>0 && push!(coords,(:zeta,0,0))
    # تمام زوج‌های واحد بادی و ساعت را برای شناسایی مختصات فعال عدم‌قطعیت بررسی می‌کند.
    for w in WT_set,h in Tau_set
        # برای خروجی بادی دارای دامنهٔ تغییر غیرصفر، مختصهٔ مستقل واحد و ساعت را اضافه می‌کند.
        wt_profile[h]*xi_wt_err_ratio>0 && push!(coords,(:wt,w,h))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # تمام زوج‌های واحد خورشیدی شبکه و ساعت را برای ساخت دامنهٔ عدم‌قطعیت بررسی می‌کند.
    for p in PV_PDN_set,h in Tau_set
        # تنها در ساعات خورشیدی با دامنهٔ غیرصفر، مختصهٔ مستقل واحد خورشیدی شبکه را اضافه می‌کند.
        pv_profile[h]*zeta_pv_err_ratio>0 && push!(coords,(:pv,p,h))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # تمام محل‌های ایستگاه و ساعت را برای شناسایی عدم‌قطعیت خورشیدی مستقل بررسی می‌کند.
    for a in 1:num_roads,h in Tau_set
        # برای هر محل ایستگاه در ساعات با تولید خورشیدی غیرصفر، مختصهٔ مستقل خروجی اضافه می‌کند.
        pv_profile[h]*zeta_pv_err_ratio>0 && push!(coords,(:station,a,h))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # تعداد دقیق تحقق‌های سه‌حالتهٔ مستقل عدم‌قطعیت را با عدد صحیح بزرگ محاسبه می‌کند.
    count=big(3)^length(coords)

    # سناریوی متناظر با اندیس مبنای سه را بدون ذخیرهٔ تمام دامنه تولید می‌کند.
    function scenario_at(index)
        # اندیس سناریو را برای تبدیل به مبنای سه در عدد صحیح بزرگ نگه می‌دارد.
        q=BigInt(index)
        # ماتریس بیت‌های انحراف مثبت و منفی باد را برای سناریوی جاری صفر آغاز می‌کند.
        wp=zeros(num_wt,num_tau);wm=copy(wp)
        # ماتریس بیت‌های انحراف مثبت و منفی خورشیدی شبکه را صفر آغاز می‌کند.
        pp=zeros(num_pv_pdn,num_tau);pm=copy(pp)
        # ماتریس بیت‌های انحراف مثبت و منفی خورشیدی ایستگاه‌ها را صفر آغاز می‌کند.
        sp=zeros(num_roads,num_tau);sm=copy(sp)
        # چهار بیت رشد تقاضا و ظرفیت تجدیدپذیر را پیش از خواندن مختصات صفر می‌کند.
        oup=0.0;oum=0.0;opp=0.0;opm=0.0
        # مختصات عدم‌قطعیت را با نوع، واحد یا محل و ساعت برای بازسازی سناریو پیمایش می‌کند.
        for (kind,row,h) in coords
            # یک رقم مبنای سه را به حالت انحراف منفی، صفر یا مثبت تبدیل می‌کند.
            digit=Int(rem(q,3))-1;q=div(q,3)
            # دو بیت مثبت و منفی متناظر با حالت سه‌گانه را می‌سازد.
            plus=Float64(digit==1);minus=Float64(digit==-1)
            # اگر مختصه مربوط به رشد تقاضاست، بیت‌های مثبت و منفی رشد تقاضا را مقداردهی می‌کند.
            if kind==:theta;oup=plus;oum=minus
            # اگر مختصه مربوط به رشد تجدیدپذیر است، بیت‌های مثبت و منفی همان رشد را مقداردهی می‌کند.
            elseif kind==:zeta;opp=plus;opm=minus
            # بیت‌های انحراف خروجی باد را در واحد و ساعت مشخص‌شده ثبت می‌کند.
            elseif kind==:wt;wp[row,h]=plus;wm[row,h]=minus
            # بیت‌های انحراف خورشیدی شبکه را در واحد و ساعت مشخص‌شده ثبت می‌کند.
            elseif kind==:pv;pp[row,h]=plus;pm[row,h]=minus
            # برای مختصهٔ خورشیدی ایستگاه، دو بیت انحراف محل و ساعت را ثبت می‌کند.
            else;sp[row,h]=plus;sm[row,h]=minus
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # تمام بیت‌های سناریوی اندیس‌گذاری‌شده را به رشد و پروفایل‌های فیزیکی تبدیل می‌کند.
        scen=create_uncertainty_scenario(\"full Phi_\$t / \$index\",t,oup,oum,opp,opm,wp,wm,pp,pm,sp,sm)
        # سناریوی ساخته‌شده را از نظر عضویت در دامنهٔ همان دوره بررسی می‌کند.
        validate_scenario(t,scen)
        # سناریوی فیزیکی اعتبارسنجی‌شده را برمی‌گرداند.
        return scen
    # تعریف تابع scenario_at را پایان می‌دهد.
    end
    # تعریف دامنهٔ تکرارپذیر را با تعداد دقیق و شناسهٔ آن برمی‌گرداند.
    return REVCSCertifiedCore.UncertaintyDomain(
        # یک تکرارگرساز تنبل و قابل شروع مجدد برای تمام اندیس‌های سناریو و تعداد دقیق آن‌ها تعریف می‌کند.
        ()->(scenario_at(i) for i in big(0):(count-1)),count,
        # شناسهٔ دامنه را به‌عنوان کل تصویر فیزیکی روابط ۴۸ تا ۵۳ و تعداد تحقق‌ها ثبت می‌کند.
        \"full Phi_\$t, Eq48-53 physical image; \$count realizations\")
# تعریف تابع full_uncertainty_domain را پایان می‌دهد.
end

# سه شبکهٔ ظرفیت را با دقت‌های ورودی صریح و واحدهای مشخص می‌سازد.
function state_grids(;charging_kw,storage_kwh,pv_kw)
    # نام کوتاه سازندهٔ شبکهٔ ظرفیت را برای سه نوع ظرفیت تعریف می‌کند.
    G=REVCSCertifiedCore.BinaryGrid
    # شبکهٔ توان شارژ و شبکهٔ انرژی باتری را با گام‌های صریح دارای واحد مناسب می‌سازد.
    return Dict(\"Cc\"=>G(0,Cc_max,charging_kw),\"Ce\"=>G(0,Ce_max,storage_kwh),
                # ورودی‌های «ظرفیت کل نصب‌شدهٔ خورشیدی ایستگاه بر حسب کیلووات» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
                \"Cv\"=>G(0,Cv_max,pv_kw))
# تعریف تابع state_grids را پایان می‌دهد.
end

# بردار حالت مشترک شامل بیت‌های وجود ایستگاه و ظرفیت‌های نصب‌شده را به مدل اضافه می‌کند.
function state_bits!(m,v,grids)
    # بردار ارجاع بیت‌های حالت خروجی دوره را خالی آغاز می‌کند.
    bits=VariableRef[]
    # فرادادهٔ ترتیب، جاده و وزن هر بیت حالت را خالی ایجاد می‌کند.
    layout=NamedTuple[]
    # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
    for a in A_set
        # بیت وجود ایستگاه را پیش از بیت‌های ظرفیت در ترتیب مشترک حالت ثبت می‌کند.
        push!(bits,v[\"z\"][a]);push!(layout,(;key=\"z\",road=a,bit=0,weight=1.0))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # سه نوع ظرفیت و همهٔ محل‌ها را با ترتیب ثابت کدگذاری حالت پیمایش می‌کند.
    for key in (\"Cc\",\"Ce\",\"Cv\"),a in A_set
        # شبکهٔ ظرفیت شارژ، باتری یا خورشیدی جاری را می‌گیرد.
        g=grids[key]
        # بیت‌های ظرفیت نصب‌شدهٔ محل جاری را می‌سازد و به متغیر فیزیکی وصل می‌کند.
        b,_=REVCSCertifiedCore.grid_variables!(m,g;physical=v[key][a])
        # هر بیت ظرفیت را برای ثبت در بردار حالت و نگاشت وزن فیزیکی پردازش می‌کند.
        for j in eachindex(b)
            # بیت ظرفیت و وزن فیزیکی آن را با همان ترتیب استاندارد در حالت ثبت می‌کند.
            push!(bits,b[j]);push!(layout,(;key,road=a,bit=j,weight=g.step*g.weights[j]))
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # بردار حالت و ترتیب دقیق اجزای آن را در خروجی مدل ذخیره می‌کند.
    v[\"state_bits\"]=bits;v[\"state_layout\"]=layout
    # ارجاع بیت‌های حالت و فرادادهٔ ترتیب آن‌ها را برمی‌گرداند.
    return bits,layout
# تعریف تابع state_bits! را پایان می‌دهد.
end

# یک حالت فیزیکی برنامه‌ریزی را با همان ترتیب استاندارد به بردار بیت تبدیل می‌کند.
function encode_state(st::StageState,grids)
    # نزدیکی جواب به مقدار صحیح یا دودویی را کنترل می‌کند تا جواب کسری به ستون یا سناریوی صحیح تبدیل نشود.
    all(x->abs(x-round(x))<1e-7,st.z[A_set]) || error(\"Nonbinary station state\")
    # پس از کنترل نزدیکی به اعداد صحیح، وضعیت وجود ایستگاه‌ها را به بیت صحیح تبدیل می‌کند.
    b=round.(Int,st.z[A_set])
    # پس از کنترل نزدیکی به عدد صحیح، فقط صفر و یک را برای وجود ایستگاه می‌پذیرد.
    all(x->x in (0,1),b) || error(\"Invalid station state\")
    # ظرفیت شارژ، انرژی باتری و خورشیدی تمام محل‌ها را با ترتیب استاندارد به بیت تبدیل می‌کند.
    for (key,values) in ((\"Cc\",st.Cc),(\"Ce\",st.Ce),(\"Cv\",st.Cv)),a in A_set
        # بیت‌های ظرفیت محل جاری را فقط در صورت عضویت مقدار در شبکه به بردار حالت اضافه می‌کند.
        append!(b,REVCSCertifiedCore.encode(grids[key],values[a]))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # بردار دودویی حالت را با ترتیب ثابت برمی‌گرداند.
    return b
# تعریف تابع encode_state را پایان می‌دهد.
end

# مدل فیزیکی را به کدگذاری حالت و تقریب پایین یا بالای آینده متصل می‌کند.
function build_certified_stage(t,prev::StageState,unc,grids;
        # جهت تقریب آینده و فهرست اختیاری برش‌های پایین را با پیش‌فرض تقریب پایین تعریف می‌کند.
        direction=:lower,lower_cuts=REVCSCertifiedCore.BinaryCut[],
        # نمونه‌های دارای کران بالا و گواه صریح دامنه را ورودی اختیاری قرار می‌دهد.
        upper_samples=REVCSCertifiedCore.UpperSample[],upper_certificate=nothing,
        # بودجهٔ زمان، تفسیر ظرفیت و مدل مشترک اختیاری را به سازندهٔ مرحله می‌دهد.
        seconds=EVAL_TIME_LIMIT,capacity_mode=CHARGING_CAPACITY_MODE,shared_model=nothing,
        initial_station_state::AbstractVector{<:Real})
    # جهت تقریب هزینهٔ آینده را به پوش پایین یا پوش بالا محدود می‌کند.
    direction in (:lower,:upper) || error(\"Invalid future-envelope direction\")
    # حالت ورودی دوره را کدگذاری می‌کند تا عضویت در شبکه و طول کد کنترل شود.
    incoming_bits=encode_state(prev,grids)
    # شرط درخواست تقریب بالایی در دورهٔ غیرپایانی را بررسی می‌کند.
    if t<num_periods && direction==:upper
        # وجود گواه صریح دامنه و کران بالایی لازم برای تقریب آینده را کنترل می‌کند.
        upper_certificate===nothing && error(\"Certified domain bound required for Eq61\")
        # همسانی شناسهٔ هدف هزینه را کنترل می‌کند تا گواه مدل، دوره یا نسخهٔ دیگری استفاده نشود.
        upper_certificate.scope==physical_cost_scope(t+1,grids;capacity_mode,initial_station_state) || error(\"Future upper certificate does not match next-stage full-Phi model, grid, initial station state, or physical assumptions\")
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # شرط وجود برش پایین در دورهٔ غیرپایانی را بررسی می‌کند.
    if t<num_periods && direction==:lower && !isempty(lower_cuts)
        # شناسهٔ مدل واقعی هزینهٔ آیندهٔ دورهٔ بعد را محاسبه می‌کند.
        target=physical_cost_scope(t+1,grids;capacity_mode,initial_station_state)
        # طول شیب تمام برش‌ها و شناسهٔ مدل هزینهٔ آیندهٔ آن‌ها را با شبکه و مرحلهٔ بعد تطبیق می‌دهد.
        all(length(c.slope)==length(incoming_bits) && c.scope==target for c in lower_cuts) ||
            # با پیام مشخص‌شده توقف می‌کند تا وضعیت فاقد گواه یا ساختار پشتیبانی‌نشده به نتیجهٔ معتبر تبدیل نشود.
            error(\"Lower cut belongs to a different future model/grid/stage\")
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # مدل فیزیکی دوره را با تمام مؤلفه‌های حالت قبلی و سناریوی جاری می‌سازد.
    m,v=build_stage_subproblem(t,prev.z,prev.Cc,prev.Ce,prev.Cv,unc;
                               # بودجهٔ زمان و تفسیر ظرفیت را با گزینهٔ ساخت در مدل مشترک به سازندهٔ فیزیکی می‌فرستد.
                               time_limit_sec=Float64(seconds),capacity_mode,shared_model,initial_station_state)
    # برای مدل عددی مستقل، شکاف هدف حل‌کننده را صفر تنظیم می‌کند؛ مهلت زمان همچنان ممکن است حل را متوقف کند.
    shared_model===nothing && set_optimizer_attribute(m,\"mip_rel_gap\",0.0)
    # حالت خروجی این دوره را به تمام بیت‌های وجود و ظرفیت متصل می‌کند.
    bits,_=state_bits!(m,v,grids)
    # شرط رسیدن به دورهٔ پایانی افق را بررسی می‌کند.
    if t==num_periods
        # در دورهٔ پایانی، هزینهٔ آیندهٔ پس از افق را دقیقاً صفر می‌کند.
        fix(v[\"alpha_cost_to_go\"],0.0;force=true)
    # در غیر این صورت، شرط انتخاب تقریب پایین هزینهٔ آینده را بررسی می‌کند.
    elseif direction==:lower
        # تمام برش‌های پایین دارای شناسهٔ هزینهٔ سازگار را به تقریب آینده اضافه می‌کند.
        for c in lower_cuts
            # صحت دودویی‌بودن مقادیر و سازگاری طول کد حالت یا فراداده را کنترل می‌کند.
            length(c.slope)==length(bits) || error(\"Binary cut layout mismatch\")
            # یک برش معتبر پایین را در فضای تمام بیت‌های حالت خروجی اعمال می‌کند.
            @constraint(m,v[\"alpha_cost_to_go\"]>=c.intercept+sum(c.slope[j]*bits[j] for j in eachindex(bits)))
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # در صورت برقرارنبودن شرط‌های پیشین، شاخهٔ جایگزین را اجرا می‌کند.
    else
        # تقریب بالایی و عضویت اجباری در دامنهٔ گواه را به مدل دوره اضافه می‌کند.
        REVCSCertifiedCore.attach_upper!(m,bits,v[\"alpha_cost_to_go\"],upper_samples,upper_certificate)
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # مدل دوره و ارجاع همهٔ متغیرها و حالت‌های کدگذاری‌شده را برمی‌گرداند.
    return m,v
# تعریف تابع build_certified_stage را پایان می‌دهد.
end

# تمام مختصات فعال عدم‌قطعیت را با زوج بیت مثبت و منفی در مدل نمادین می‌سازد.
function symbolic_uncertainty(m,t)
    # پیش از ساخت بیت‌های نمادین، شمارهٔ دورهٔ برنامه‌ریزی را کنترل می‌کند.
    t in T_set || error(\"Invalid stage\")
    # شرط دورهٔ نخست و قطعی برنامه‌ریزی را بررسی می‌کند.
    if t==1
        # تنها سناریوی قطعی دورهٔ نخست را از دامنه می‌گیرد.
        root=first(full_uncertainty_domain(1).factory())
        # برای دورهٔ قطعی، بیت عدم‌قطعیت نمی‌سازد و تابع استخراج یک کپی سناریو را می‌دهد.
        return VariableRef[],root,()->deepcopy(root)
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # فهرست مختصات فعال عدم‌قطعیت را شامل نوع، شمارهٔ واحد یا محل و ساعت خالی ایجاد می‌کند.
    coords=Tuple{Symbol,Int,Int}[]
    # اگر خطای رشد تقاضا غیرصفر باشد، یک مختصهٔ مستقل رشد تقاضا اضافه می‌کند.
    theta_err[t]>0 && push!(coords,(:theta,0,0))
    # اگر خطای رشد ظرفیت تجدیدپذیر غیرصفر باشد، یک مختصهٔ مستقل رشد ظرفیت اضافه می‌کند.
    zeta_err[t]>0 && push!(coords,(:zeta,0,0))
    # تمام زوج‌های واحد بادی و ساعت را برای شناسایی مختصات فعال عدم‌قطعیت بررسی می‌کند.
    for w in WT_set,h in Tau_set
        # برای خروجی بادی دارای دامنهٔ تغییر غیرصفر، مختصهٔ مستقل واحد و ساعت را اضافه می‌کند.
        wt_profile[h]*xi_wt_err_ratio>0 && push!(coords,(:wt,w,h))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # تمام زوج‌های واحد خورشیدی شبکه و ساعت را برای ساخت دامنهٔ عدم‌قطعیت بررسی می‌کند.
    for p in PV_PDN_set,h in Tau_set
        # تنها در ساعات خورشیدی با دامنهٔ غیرصفر، مختصهٔ مستقل واحد خورشیدی شبکه را اضافه می‌کند.
        pv_profile[h]*zeta_pv_err_ratio>0 && push!(coords,(:pv,p,h))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # تمام محل‌های ایستگاه و ساعت را برای شناسایی عدم‌قطعیت خورشیدی مستقل بررسی می‌کند.
    for a in 1:num_roads,h in Tau_set
        # برای هر محل ایستگاه در ساعات با تولید خورشیدی غیرصفر، مختصهٔ مستقل خروجی اضافه می‌کند.
        pv_profile[h]*zeta_pv_err_ratio>0 && push!(coords,(:station,a,h))
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # برای هر مختصهٔ فعال عدم‌قطعیت، دو بیت انحراف مثبت و منفی ایجاد می‌کند.
    z=@variable(m,[1:2length(coords)],Bin)
    # رشدهای نمادین تقاضا و ظرفیت تجدیدپذیر را از پیش‌بینی آغاز می‌کند.
    theta=AffExpr(theta_fc[t]);growth=AffExpr(zeta_fc[t])
    # پروفایل پایهٔ همهٔ واحدهای بادی را در ماتریس پذیرندهٔ عبارت نمادین قرار می‌دهد.
    wt=Matrix{Any}(repeat(wt_profile',num_wt,1))
    # پروفایل پایهٔ واحدهای خورشیدی شبکه را برای افزودن عبارت نمادین آماده می‌کند.
    pv=Matrix{Any}(repeat(pv_profile',num_pv_pdn,1))
    # پروفایل خورشیدی تمام محل‌های ایستگاه را برای عدم‌قطعیت مستقل آماده می‌کند.
    station=Matrix{Any}(repeat(pv_profile',num_roads,1))
    # هر مختصهٔ فعال عدم‌قطعیت را با شمارهٔ زوج بیت متناظر آن پردازش می‌کند.
    for (i,(kind,r,h)) in enumerate(coords)
        # دو بیت مثبت و منفی مختصهٔ جاری را از بردار مشترک می‌گیرد.
        p=z[2i-1];n=z[2i]
        # نمایش تکراری انحراف صفر با هر دو بیت یک را حذف می‌کند؛ تصویر فیزیکی سه‌حالته محدودتر نمی‌شود.
        @constraint(m,p+n<=1)
        # انحراف نمادین رشد تقاضای سفر را از اختلاف دو بیت به پیش‌بینی اضافه می‌کند.
        if kind==:theta;theta+=theta_err[t]*(p-n)
        # انحراف نمادین رشد ظرفیت تجدیدپذیر را به پیش‌بینی اضافه می‌کند.
        elseif kind==:zeta;growth+=zeta_err[t]*(p-n)
        # انحراف نمادین خروجی بادی واحد و ساعت جاری را به پروفایل پایه اضافه می‌کند.
        elseif kind==:wt;wt[r,h]+=wt_profile[h]*xi_wt_err_ratio*(p-n)
        # انحراف نمادین خروجی خورشیدی شبکه را برای واحد و ساعت جاری اضافه می‌کند.
        elseif kind==:pv;pv[r,h]+=pv_profile[h]*zeta_pv_err_ratio*(p-n)
        # انحراف نمادین خورشیدی محل ایستگاه را برای ساعت جاری اضافه می‌کند.
        else;station[r,h]+=pv_profile[h]*zeta_pv_err_ratio*(p-n)
        # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # سناریوی نمادین کل دامنه را با عبارت رشد تقاضای سفر در یک فرهنگ داده آغاز می‌کند.
    unc=Dict{String,Any}(\"name\"=>\"symbolic full Phi_\$t\",\"theta_t\"=>theta,
        # ورودی‌های «zeta_t، xi_wt، zeta_pv، zeta_station_pv» را در فرهنگ دادهٔ خروجی ثبت می‌کند.
        \"zeta_t\"=>growth,\"xi_wt\"=>wt,\"zeta_pv\"=>pv,\"zeta_station_pv\"=>station)

    # سناریوی فیزیکی متناظر با جواب صحیح مستر نمادین را استخراج و اعتبارسنجی می‌کند.
    function extract()
        # مقدار بیت‌های عدم‌قطعیت جواب مستر را استخراج می‌کند.
        vals=value.(z)
        # نزدیکی جواب به مقدار صحیح یا دودویی را کنترل می‌کند تا جواب کسری به ستون یا سناریوی صحیح تبدیل نشود.
        maximum(abs.(vals.-round.(vals));init=0.0)<=1e-5 || error(\"Nonbinary adversarial realization\")
        # ماتریس‌های مثبت و منفی باد و خورشیدی شبکه را برای استخراج سناریوی جواب صفر می‌کند.
        wp=zeros(num_wt,num_tau);wm=copy(wp);pp=zeros(num_pv_pdn,num_tau);pm=copy(pp)
        # ماتریس بیت‌های انحراف مثبت و منفی خورشیدی ایستگاه‌ها را صفر آغاز می‌کند.
        sp=zeros(num_roads,num_tau);sm=copy(sp)
        # چهار بیت رشد تقاضا و ظرفیت تجدیدپذیر را پیش از خواندن مختصات صفر می‌کند.
        oup=0.0;oum=0.0;opp=0.0;opm=0.0
        # هر مختصهٔ فعال عدم‌قطعیت را با شمارهٔ زوج بیت متناظر آن پردازش می‌کند.
        for (i,(kind,r,h)) in enumerate(coords)
            # پس از کنترل صحیح‌بودن، بیت‌های مثبت و منفی این مختصه را به صفر و یک تبدیل می‌کند.
            p=Float64(round(vals[2i-1]));n=Float64(round(vals[2i]))
            # بیت‌های استخراج‌شدهٔ مختصهٔ رشد تقاضا را در فرادادهٔ سناریو ثبت می‌کند.
            if kind==:theta;oup=p;oum=n
            # بیت‌های استخراج‌شدهٔ مختصهٔ رشد تجدیدپذیر را در فراداده ثبت می‌کند.
            elseif kind==:zeta;opp=p;opm=n
            # بیت‌های جواب مستر را در مختصهٔ خروجی بادی متناظر ثبت می‌کند.
            elseif kind==:wt;wp[r,h]=p;wm[r,h]=n
            # بیت‌های جواب مستر را در مختصهٔ خورشیدی شبکه ثبت می‌کند.
            elseif kind==:pv;pp[r,h]=p;pm[r,h]=n
            # بیت‌های جواب مستر را برای محل و ساعت خورشیدی ایستگاه ثبت می‌کند.
            else;sp[r,h]=p;sm[r,h]=n
            # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
            end
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # سناریوی فیزیکی متناظر با جواب کامل مستر نمادین را از بیت‌های استخراج‌شده می‌سازد.
        sc=create_uncertainty_scenario(\"native full Phi_\$t\",t,oup,oum,opp,opm,wp,wm,pp,pm,sp,sm)
        # سناریوی استخراج‌شده از مستر را با دامنهٔ فیزیکی و فرادادهٔ دودویی تطبیق می‌دهد.
        validate_scenario(t,sc)
        # سناریوی فیزیکی استخراج‌شده و اعتبارسنجی‌شده را برمی‌گرداند.
        return sc
    # تعریف تابع extract را پایان می‌دهد.
    end
    # بیت‌های عدم‌قطعیت، سناریوی نمادین و تابع استخراج جواب را برمی‌گرداند.
    return z,unc,extract
# تعریف تابع symbolic_uncertainty را پایان می‌دهد.
end

# رابط حل یک دوره روی کل عدم‌قطعیت با C&CG نمادین را تعریف می‌کند.
function solve_native_stage(t,prev,grids;
        # جهت تقریب آینده و فهرست اختیاری برش‌های پایین را با پیش‌فرض تقریب پایین تعریف می‌کند.
        direction=:lower,lower_cuts=REVCSCertifiedCore.BinaryCut[],
        # نمونه‌های دارای کران بالا و گواه صریح دامنه را ورودی اختیاری قرار می‌دهد.
        upper_samples=REVCSCertifiedCore.UpperSample[],upper_certificate=nothing,
        # SCIP را حل‌کنندهٔ پیش‌فرض مستر و سقف تکرار، زمان هر حل و تلرانس را ورودی قرار می‌دهد.
        optimizer=nothing,max_iters=100,seconds=EVAL_TIME_LIMIT,rtol=rddp_gap_tol,
        # تفسیر انتخاب‌شدهٔ ظرفیت شارژ را برای این فراخوانی ثبت می‌کند.
        capacity_mode=CHARGING_CAPACITY_MODE,initial_station_state::AbstractVector{<:Real})
    # تابع ساخت مدل عددی در هر سناریو را با حالت قبلی و تقریب آیندهٔ ثابت تعریف می‌کند.
    builder=u->first(build_certified_stage(t,prev,u,grids;direction,lower_cuts,
        # نمونه‌ها و گواه آینده، بودجهٔ زمان، تفسیر ظرفیت و وضعیت اولیه را می‌فرستد.
        upper_samples,upper_certificate,seconds,capacity_mode,initial_station_state))
    # تابع افزودن همان بلوک مرحله را در مدل مشترک نمادین تعریف می‌کند.
    block=(m,u)->build_certified_stage(t,prev,u,grids;direction,lower_cuts,
        # همهٔ تنظیمات مدل عددی را با ارجاع مدل مشترک به بلوک نمادین منتقل می‌کند.
        upper_samples,upper_certificate,seconds,capacity_mode,initial_station_state,shared_model=m)
    # تعریف کامل دامنهٔ عدم‌قطعیت دورهٔ جاری را می‌گیرد؛ در مسیر نمادین آن را پیمایش کامل نمی‌کند.
    domain=full_uncertainty_domain(t)
    # اولین تحقق مجاز دامنه را به‌عنوان سناریوی آغازین C&CG انتخاب می‌کند.
    seed=first(domain.factory())
    # شناسهٔ دقیق هدف هزینهٔ دوره با شبکه، عدم‌قطعیت و فرض ظرفیت جاری را می‌سازد.
    scope=physical_cost_scope(t,grids;domain,capacity_mode,initial_station_state)
    # شرط دورهٔ نخست و قطعی برنامه‌ریزی را بررسی می‌کند.
    if t==1
        # در دورهٔ اول قطعی، همان MILP را مستقیم حل می‌کند و مستر نامطمئن غیرضروری نمی‌سازد.
        m=builder(seed);REVCSCertifiedCore.solve_tracked!(m;context=\"deterministic root\")
        # دو کران حل مستقیم ریشهٔ قطعی را با کنترل وضعیت حل می‌خواند.
        row=REVCSCertifiedCore.min_bounds(m)
        # فهرست الگوهای صحیح ثبت‌شدهٔ ریشه را خالی آغاز می‌کند.
        columns=REVCSCertifiedCore.IntegerPattern[]
        # فقط در صورت داشتن جواب قابل قبول، الگوی صحیح ریشه را ذخیره می‌کند.
        row.feasible && push!(columns,REVCSCertifiedCore.integer_pattern(m))
        # یک سطر تاریخچهٔ حل مستقیم دورهٔ قطعی با کران‌های واقعی می‌سازد.
        history=NamedTuple[(;iteration=1,lower=row.lower,upper=row.upper,
            # وضعیت بهینگی و تعداد الگوهای ریشه را با برچسب حل قطعی ثبت می‌کند.
            master_complete=row.status==MOI.OPTIMAL,columns=length(columns),phase=:deterministic)]
        # کران‌ها، شاهد، تاریخچه و علت توقف C&CG را با همان نقش و دامنهٔ ثبت‌شده برمی‌گرداند.
        if direction==:upper && row.status==MOI.INFEASIBLE
            # The codebook may be responsible: do not certify robust
            # physical infeasibility of a codebook-restricted root.
            return REVCSCertifiedCore.CCGResult(-Inf,Inf,false,false,seed,
                columns,history,scope,:upper_codebook_or_physical_infeasible,direction)
        end
        return REVCSCertifiedCore.CCGResult(row.lower,row.upper,
            REVCSCertifiedCore.gap_closed(row.lower,row.upper,rtol),row.status==MOI.INFEASIBLE,
            seed,columns,history,scope,:deterministic_root,direction)
    # شاخه‌های شرط جاری را می‌بندد و به دستور بعدی می‌رود.
    end
    # A deterministic Stage-1 root has already returned above; only stages >=2
    # may need the native optimality master and SCIP optimizer.
    optimizer === nothing && (optimizer=g7_scip_optimizer())
    # C&CG نمادین را با مدل عددی پاسخ و نمایش کامل عدم‌قطعیت فراخوانی می‌کند.
    return REVCSCertifiedCore.solve_native_ccg(builder,m->symbolic_uncertainty(m,t),block,seed;
        # نقش هزینه را در دورهٔ پایانی دقیق و در سایر دوره‌ها مطابق جهت تقریب آینده ثبت می‌کند.
        optimizer,scope,max_iters,seconds,rtol,bound_role=t==num_periods ? :exact : direction)
# تعریف تابع solve_native_stage را پایان می‌دهد.
end

# رابط مرجع حل دوره با مستر پیمایشی را تعریف می‌کند؛ برای دامنهٔ کامل بسیار بزرگ عملی نیست.
function solve_certified_stage(t,prev,grids; domain=full_uncertainty_domain(t),
        # جهت تقریب آینده و فهرست اختیاری برش‌های پایین را با پیش‌فرض تقریب پایین تعریف می‌کند.
        direction=:lower,lower_cuts=REVCSCertifiedCore.BinaryCut[],
        # نمونه‌های دارای کران بالا و گواه صریح دامنه را ورودی اختیاری قرار می‌دهد.
        upper_samples=REVCSCertifiedCore.UpperSample[],upper_certificate=nothing,
        # سقف تکرار و تعداد سناریوهای مجاز پیمایش در مستر مرجع و مهلت هر حل را تعریف می‌کند.
        max_iters=100,max_master_scenarios=10000,seconds=EVAL_TIME_LIMIT,
        # تلرانس شکاف و تفسیر ظرفیت را به رابط مرجع منتقل می‌کند.
        rtol=rddp_gap_tol,capacity_mode=CHARGING_CAPACITY_MODE,
        initial_station_state::AbstractVector{<:Real})
    # تابع ساخت مدل عددی در هر سناریو را با حالت قبلی و تقریب آیندهٔ ثابت تعریف می‌کند.
    builder=u->first(build_certified_stage(t,prev,u,grids;direction,lower_cuts,
        # نمونه‌ها و گواه آینده، بودجهٔ زمان، تفسیر ظرفیت و وضعیت اولیه را می‌فرستد.
        upper_samples,upper_certificate,seconds,capacity_mode,initial_station_state))
    # همان دامنهٔ سناریو را با شناسهٔ دقیق مدل هزینه برای نتیجهٔ مرجع بسته‌بندی می‌کند.
    scoped_domain=REVCSCertifiedCore.UncertaintyDomain(domain.factory,domain.cardinality,
        # امضای دوره، شبکه، دامنه و فرض ظرفیت را برای هویت نتیجهٔ مرجع تعیین می‌کند.
        physical_cost_scope(t,grids;domain,capacity_mode,initial_station_state))
    # C&CG پیمایشی مرجع را با بودجهٔ صریح مستر اجرا می‌کند؛ دامنهٔ ناقص کران بالا نمی‌سازد.
    r=REVCSCertifiedCore.solve_ccg(builder,scoped_domain;max_iters,max_master_scenarios,seconds,rtol,
        # نقش نتیجهٔ مرجع را برای دورهٔ پایانی دقیق و برای دوره‌های دیگر مطابق تقریب آینده تعیین می‌کند.
        bound_role=t==num_periods ? :exact : direction)
    # نتیجه و تنظیمات مؤثر در تفسیر کران‌های آن را یک‌جا برمی‌گرداند.
    return (;result=r,direction,grids,capacity_mode,
        # دامنهٔ اعتبار تقریب آینده را در خروجی ثبت می‌کند؛ بالایی به کدبوک تحمیل‌شده و پایینی به پوش پایین مربوط است.
        cost_scope=direction==:upper ? \"certified UPPER future envelope on enforced codebook\" : \"LOWER future envelope only\")
# تعریف تابع solve_certified_stage را پایان می‌دهد.
end

# تمام وابستگی‌های حالت قبلی را با نسخه‌های دودویی آزاد برای برش لاگرانژی جایگزین می‌کند.
function binary_predecessor_builder(t,prev,unc,grids;
        # برش‌های پایین موجود و بودجهٔ زمان ساخت برش لاگرانژی را ورودی اختیاری می‌گیرد.
        lower_cuts=REVCSCertifiedCore.BinaryCut[],seconds=EVAL_TIME_LIMIT,
        # تفسیر انتخاب‌شدهٔ ظرفیت شارژ را برای این فراخوانی ثبت می‌کند.
        capacity_mode=CHARGING_CAPACITY_MODE,initial_station_state::AbstractVector{<:Real})
    # ساخت برش هزینه نسبت به حالت قبلی را فقط برای دوره‌های پس از ریشه مجاز می‌کند.
    t>1 || error(\"Root has no predecessor cost-to-go cut\")
    # مدل مرحله با تقریب پایین آینده را پیش از آزادسازی همهٔ مؤلفه‌های حالت قبلی می‌سازد.
    m,v=build_certified_stage(t,prev,unc,grids;lower_cuts,seconds,capacity_mode,initial_station_state)
    # بردار تمام بیت‌های نسخهٔ آزاد حالت قبلی را خالی آغاز می‌کند.
    beta=VariableRef[]
    # نگاشت مؤلفه و جاده به نسخهٔ آزاد حالت قبلی را ایجاد می‌کند.
    copies=Dict{Tuple{String,Int},Any}()
    # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
    for a in A_set
        # برای وضعیت وجود ایستگاه قبلی، یک بیت آزاد مستقل می‌سازد و در بردار لاگرانژی ثبت می‌کند.
        b=@variable(m,binary=true);push!(beta,b);copies[(\"z\",a)]=b
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # سه نوع ظرفیت و همهٔ محل‌ها را با ترتیب ثابت کدگذاری حالت پیمایش می‌کند.
    for key in (\"Cc\",\"Ce\",\"Cv\"),a in A_set
        # تمام بیت‌های ظرفیت قبلی را بدون تثبیت به نقطهٔ مرجع ایجاد می‌کند.
        b,x=REVCSCertifiedCore.grid_variables!(m,grids[key])
        # بیت‌های ظرفیت قبلی و عبارت فیزیکی متناظر را در ترتیب استاندارد ثبت می‌کند.
        append!(beta,b);copies[(key,a)]=x
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # روی همهٔ محل‌های کاندید ایستگاه حلقه می‌زند.
    for a in A_set
        # همهٔ مؤلفه‌های حالت قبلی، شامل وجود ایستگاه و سه ظرفیت، را برای جایگزینی قیود اتصال پیمایش می‌کند.
        for key in (\"z\",\"Cc\",\"Ce\",\"Cv\")
            # مرجع قید اتصال مؤلفهٔ حالت قبلی را پیدا می‌کند.
            c=v[\"link_\"*key][a]
            # عبارت قید اتصال پیشین را پیش از جایگزینی می‌خواند.
            obj=constraint_object(c)
            # سمت چپ قید اتصال را برای حذف قید قدیمی نگه می‌دارد.
            lhs=copy(obj.func)
            # قید وابسته به مقدار ثابت حالت قبلی را از مدل حذف می‌کند.
            delete(m,c)
            # همان رابطهٔ اتصال را به نسخهٔ آزاد و دودویی مؤلفهٔ حالت قبلی وصل می‌کند.
            @constraint(m,lhs==copies[(key,a)])
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
        # همهٔ قیود مستقیم وابسته به ظرفیت قبلی در جاده‌ها و ساعت‌ها را نیز برای جایگزینی بررسی می‌کند.
        for ((road,h),c) in v[\"predecessor_capacity_links\"]
            # فقط قیود مستقیم ظرفیت مربوط به جادهٔ جاری را جایگزین می‌کند.
            road==a || continue
            # سمت چپ قید مستقیم ظرفیت شارژ را پیش از حذف نگه می‌دارد.
            obj=constraint_object(c);lhs=copy(obj.func)
            # قید وابسته به مقدار ثابت حالت قبلی را از مدل حذف می‌کند.
            delete(m,c)
            # وابستگی مستقیم معادلهٔ ۳۳ به ظرفیت قبلی را نیز به نسخهٔ دودویی وصل می‌کند تا ثابت پنهان باقی نماند.
            @constraint(m,lhs<=copies[(\"Cc\",a)])
        # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
        end
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # مدل لاگرانژی و تمام بیت‌های آزاد حالت قبلی را برمی‌گرداند.
    return m,beta
# تعریف تابع binary_predecessor_builder را پایان می‌دهد.
end

# تولید برش لاگرانژی با کنترل سناریو و شناسهٔ هدف هزینه را تعریف می‌کند.
function certified_lagrangian_cut(t,prev,unc,grids;
        # برش‌های پایین موجود و بودجهٔ زمان ساخت برش لاگرانژی را ورودی اختیاری می‌گیرد.
        lower_cuts=REVCSCertifiedCore.BinaryCut[],seconds=EVAL_TIME_LIMIT,
        # تفسیر ظرفیت و سایر تنظیمات روش سطح را به رابط ساخت برش می‌پذیرد.
        capacity_mode=CHARGING_CAPACITY_MODE,initial_station_state::AbstractVector{<:Real},kwargs...)
    # مجازبودن سناریوی استفاده‌شده برای ساخت برش پایین را بررسی می‌کند.
    validate_scenario(t,unc)
    # حالت قبلی مرجع را دقیقاً با همان شبکه و ترتیب بیت‌ها کدگذاری می‌کند.
    anchor=encode_state(prev,grids)
    # تابع ساخت مدل دارای نسخه‌های دودویی آزاد تمام حالت قبلی را برای اوراکل لاگرانژی تعریف می‌کند.
    builder=()->binary_predecessor_builder(t,prev,unc,grids;lower_cuts,seconds,capacity_mode,initial_station_state)
    # اوراکل MILP و روش سطح را برای تولید برش پایین در حالت مرجع فراخوانی می‌کند.
    return REVCSCertifiedCore.lagrangian_cut(builder,anchor;seconds,
        # شناسهٔ هزینهٔ برش را با مدل همان دوره یکسان کرده و سایر تنظیمات روش سطح را منتقل می‌کند.
        scope=physical_cost_scope(t,grids;capacity_mode,initial_station_state),kwargs...)
# تعریف تابع certified_lagrangian_cut را پایان می‌دهد.
end

# رابط حل تقریب بالایی را به حل‌کنندهٔ C&CG نمادین متصل می‌کند.
function solve_upper_approximation_stage(t::Int,prev::StageState,
        # شبکه‌های صریح ظرفیت و نمونه‌های واقعاً دارای کران بالای گواه را ورودی رابط بالا قرار می‌دهد.
        grids::Dict,samples::Vector{REVCSCertifiedCore.UpperSample},
        # وجود گواه صریح دامنه را در نوع ورودی الزامی و سایر تنظیمات حل را قابل انتقال می‌کند.
        certificate::REVCSCertifiedCore.DomainUpperCertificate;kwargs...)
    # حل تقریب بالایی را با جهت upper به C&CG نمادین مرحله می‌فرستد.
    return solve_native_stage(t,prev,grids;direction=:upper,
        # نمونه‌ها و گواه دامنه را بدون تبدیل هزینهٔ مسیر به گواه مقاوم منتقل می‌کند.
        upper_samples=samples,upper_certificate=certificate,kwargs...)
# تعریف تابع solve_upper_approximation_stage را پایان می‌دهد.
end

# هزینه‌های بالایی آینده را برای حالت‌های مشخص از عقب به جلو گواهی می‌کند.
function certify_future_samples(t,states::Vector{StageState},grids;
        # نمونه‌ها و گواه هزینهٔ مراحل بعدتر را برای گواهی از عقب به جلو دریافت می‌کند.
        successor_samples=REVCSCertifiedCore.UpperSample[],successor_certificate=nothing,
        # مهلت حل هر مدل، سقف تکرار C&CG و تلرانس شکاف نمونه‌ها را تعریف می‌کند.
        seconds=EVAL_TIME_LIMIT,max_iters=100,rtol=rddp_gap_tol,
        # حل‌کنندهٔ شاخص‌پذیر مستر، تفسیر ظرفیت و مبنای اولیه را برای گواهی نمونه‌ها مشخص می‌کند.
        optimizer=nothing,capacity_mode=CHARGING_CAPACITY_MODE,
        initial_station_state::AbstractVector{<:Real})
    # گواهی هزینهٔ آینده را فقط برای حالت خروجی دوره‌های غیرپایانی تعریف می‌کند.
    1<=t<num_periods || error(\"Samples represent a nonterminal state's future cost\")
    # نبود حالت‌های صریح برای گواهی نمونه‌های بالایی را خطا اعلام می‌کند.
    isempty(states) && error(\"No candidate planning states\")
    # همهٔ حالت‌های نمونه را روی شبکهٔ مشخص به بیت تبدیل می‌کند.
    bits=[encode_state(s,grids) for s in states]
    # یکتابودن کد حالت‌ها را کنترل می‌کند تا گواه دامنه و نمونه‌ها تکرار مبهم نداشته باشد.
    length(unique(REVCSCertifiedCore.binary_key.(bits)))==length(bits) || error(\"Duplicate sample state\")
    # محل نگهداری نتیجهٔ مقاوم دارای کران برای هر حالت نمونه را ایجاد می‌کند.
    results=Dict{String,REVCSCertifiedCore.CCGResult}()
    # هر حالت فیزیکی نمونه را همراه کد دودویی متناظر آن برای حل مقاوم آینده پردازش می‌کند.
    for (state,b) in zip(states,bits)
        # برای حالت ثابت نمونه، هزینهٔ مقاوم آینده را از دورهٔ بعد با تقریب بالایی حل می‌کند.
        r=solve_native_stage(t+1,state,grids;direction=:upper,
            # نمونه‌ها و گواه معتبر مراحل بعدتر را به هزینهٔ آیندهٔ این نمونه وصل می‌کند.
            upper_samples=successor_samples,upper_certificate=successor_certificate,
            # تنظیمات حل، فرض ظرفیت و وضعیت اولیه را در تمام گام‌های گواهی یکسان نگه می‌دارد.
            seconds,max_iters,rtol,optimizer,capacity_mode,initial_station_state)
        # متناهی‌بودن مقدار لازم برای ادامهٔ کران‌سازی را کنترل می‌کند؛ مقدار نامعلوم جایگزین عددی نمی‌شود.
        isfinite(r.upper) && !r.infeasible || error(\"State at stage \$t has no certified finite future upper cost; status=\$(r.reason)\")
        # نتیجهٔ حل هزینهٔ آینده را با کلید حالت ورودی ثبت می‌کند.
        results[REVCSCertifiedCore.binary_key(b)]=r
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # از کران‌های بالای واقعی نمونه‌ها، گواه یکنواخت همان دامنهٔ صریح را می‌سازد.
    cert=REVCSCertifiedCore.certify_upper_domain(bits,b->results[REVCSCertifiedCore.binary_key(b)])
    # فقط از نتایج مقاوم با نقش مجاز، نمونه‌های دارای کران بالای گواه می‌سازد.
    samples=[REVCSCertifiedCore.UpperSample(b,results[REVCSCertifiedCore.binary_key(b)]) for b in bits]
    # نمونه‌ها، گواه دامنه و نتایج پایهٔ قابل بررسی را یک‌جا برمی‌گرداند.
    return (;samples,certificate=cert,results)
# تعریف تابع certify_future_samples را پایان می‌دهد.
end

# گزارش پیکربندی و محدودیت ادعای همگرایی این فایل را تعریف می‌کند.
function certified_configuration_report()
    # به‌صراحت اعلام می‌کند که گزارش حاضر ادعای همگرایی اجرای کامل شبکه ندارد.
    println(\"REVCS19 Gate 7 C&CG integration candidate; no full-scale convergence claim\")
    println(\"Plan mode requires explicit --initial-state=paper_zero or existing_five.\")
    # لزوم تعیین صریح دقت شبکهٔ ظرفیت به‌وسیلهٔ فراخواننده را اعلام می‌کند.
    println(\"Grid precision must be explicitly supplied to state_grids.\")
    # روی همهٔ دوره‌های برنامه‌ریزی حلقه می‌زند.
    for t in T_set
        # تعداد دقیق تحقق‌های دامنهٔ کامل دوره را برای گزارش، بدون پیمایش آن‌ها، می‌گیرد.
        d=full_uncertainty_domain(t)
        # تعداد دقیق تحقق‌های عدم‌قطعیت هر دوره را بدون حل یا پیمایش تمام آن‌ها چاپ می‌کند.
        println(\"stage \$t: \",d.cardinality,\" uncertainty realizations\")
    # حلقهٔ جاری را پایان می‌دهد و اجرای بلوک بیرونی را ادامه می‌دهد.
    end
    # رابط حل با کل بیت‌های عدم‌قطعیت و شاخص‌های بومی SCIP را معرفی می‌کند.
    println(\"Native C&CG: solve_native_stage uses full binary uncertainty and native indicators (SCIP).\")
    # نقش مرجع نسخهٔ پیمایشی و غیرعملی‌بودن پیمایش کل دامنهٔ بزرگ را اعلام می‌کند.
    println(\"Enumeration-master solve_certified_stage is an exact REFERENCE backend; the full uncertainty domain is intractable for enumeration.\")
    # تفاوت کران‌های تقریب پایین یا مستر ناقص با کران بالای مقاوم هدف اصلی را در خروجی یادآوری می‌کند.
    println(\"Do not report a truncated master scan or a lower-envelope upper bound as the paper's robust UB.\")
# تعریف تابع certified_configuration_report را پایان می‌دهد.
end

# موتور چندمرحله‌ای: آرشیو شمارهٔ t تقریب Q_t بر حالت ورودی دورهٔ t است.
const RC = REVCSCertifiedCore
# مسیر پوشش کامل فقط گواهی را می‌پذیرد که با ارزیابی تمام فضای دودویی ساخته شده باشد.
function solve_upper_approximation_stage(t::Int,prev::StageState,grids::Dict,
        samples::Vector{RC.UpperSample},certificate::RC.FullBinaryUpperCertificate;kwargs...)
    solve_native_stage(t,prev,grids;direction=:upper,upper_samples=samples,
        upper_certificate=certificate,kwargs...)
end
struct PlanningProblem
    horizon::Int
    initial::Any
    encode::Function
    scope::Function
    oracle::Function
    build::Function
    cut::Function
    validate::Function
    decode::Function
end
# رمزگشا برای بازتأیید واردات لازم است؛ ساخت مسئله بدون آن همچنان برای حل تازه مجاز است.
PlanningProblem(T,initial,encode,scope,oracle,build,cut,validate)=PlanningProblem(
    T,initial,encode,scope,oracle,build,cut,validate,
    b->error(\"A state decoder is required for policy revalidation\"))
mutable struct PlanningArchive
    cuts::Vector{Vector{RC.BinaryCut}}
    upper::Vector{Dict{String,RC.UpperSample}}
    responders::Vector{Dict{String,Vector{RC.IntegerPattern}}}
end
PlanningArchive(T::Int)=PlanningArchive([RC.BinaryCut[] for _ in 1:T+1],
    [Dict{String,RC.UpperSample}() for _ in 1:T+1],
    [Dict{String,Vector{RC.IntegerPattern}}() for _ in 1:T+1])

# نمونه‌های خارج از کدبوک هزینهٔ بالایی +Inf دارند؛ محدودکردن تصمیم‌ها فقط برای UB است.
function future_envelope(a::PlanningArchive,t)
    samples=sort!(collect(values(a.upper[t+1]));by=s->RC.binary_key(s.bits))
    certificate=isempty(samples) ? nothing : RC.DomainUpperCertificate(
        [s.bits for s in samples],maximum(s.value for s in samples),first(samples).scope)
    return (;lower_cuts=a.cuts[t+1],upper_samples=samples,upper_certificate=certificate)
end
function archive_upper!(a,t,b,r,target)
    r.scope==target || error(\"Upper result target mismatch\")
    r.bound_role in (:upper,:exact) || error(\"A lower-envelope incumbent cannot certify a policy\")
    isfinite(r.upper) && !r.infeasible || return false
    key=RC.binary_key(b)
    if !haskey(a.upper[t],key) || r.upper<a.upper[t][key].value
        a.upper[t][key]=RC.UpperSample(b,r)
        # تنها ستون‌های حل واقعی متناظر با همین کران ذخیره می‌شوند.
        a.responders[t][key]=deepcopy(r.columns)
        return true
    end
    return false
end
function unavailable_upper(p,t,reason=:missing_upper_samples)
    RC.CCGResult(-Inf,Inf,false,false,nothing,RC.IntegerPattern[],NamedTuple[],p.scope(t),reason,:upper)
end

function invalidate_upper_after_repair!(a::PlanningArchive)
    for t in eachindex(a.upper)
        empty!(a.upper[t])
        empty!(a.responders[t])
    end
    return nothing
end
function planning_oracle(p::PlanningProblem,a::PlanningArchive,t,prev,direction;kwargs...)
    direction==:upper && t<p.horizon && isempty(a.upper[t+1]) &&
        return unavailable_upper(p,t,:upper_codebook_missing)
    env=future_envelope(a,t)
    r=p.oracle(t,prev;direction,env...,kwargs...)
    r.scope==p.scope(t) || error(\"Oracle changed its target\")
    if direction==:upper && t<p.horizon && r.infeasible
        # The upper-only codebook restriction may have caused infeasibility;
        # no unconditional robust-infeasibility statement may escape here.
        return unavailable_upper(p,t,:upper_codebook_or_physical_infeasible)
    end
    return r
end

# Exact exclusion of a predecessor state with a proven infeasible final recourse.
# This is a forward feasibility safeguard, not an RDDP value-function cut.
function add_exact_feasibility_nogoods!(m::Model, forbidden::Vector{Vector{Int}})
    isempty(forbidden) && return 0
    registered = object_dictionary(m)
    haskey(registered, :revcs_output_state_bits) ||
        error(\"Exact output-state bits are not registered by the physical builder\")
    bits = registered[:revcs_output_state_bits]
    for code in forbidden
        length(code)==length(bits) || error(\"Feasibility no-good bit length mismatch\")
        all(x->x in (0,1),code) || error(\"Nonbinary forbidden state\")
        @constraint(m, sum(code[j]==1 ? 1-bits[j] : bits[j]
                           for j in eachindex(code)) >= 1)
    end
    return length(forbidden)
end

# A feasible incumbent under TIME_LIMIT is not an optimal Forward decision.
# Exploratory acceptance is a separate, explicitly noncertifying mode.
function forward_optimality_gate(status,feasible,budget_ok;require_optimal::Bool=true)
    return feasible && budget_ok && (!require_optimal || status==MOI.OPTIMAL)
end

# تصمیم هر مرحله فقط حالت گذشته، مشاهدهٔ جاری و آرشیو ثابت سیاست را می‌بیند.
function planning_decision(p::PlanningProblem,a::PlanningArchive,t,prev,u;
        direction=:lower,seconds=600.,capture=false,response_order=:portfolio_first,
        forbidden_state_bits::Vector{Vector{Int}}=Vector{Int}[],
        recourse_witnesses::Vector{Dict{String,Any}}=Dict{String,Any}[],
        require_optimal::Bool=true)
    started=time()
    direction in (:lower,:upper) || error(\"Unknown decision direction\")
    response_order in (:portfolio_first,:milp_first,:portfolio_only) || error(\"Unknown response order\")
    seconds>0 || error(\"Positive time per response attempt required\")
    p.validate(t,u)
    env=future_envelope(a,t)
    direction==:upper && t<p.horizon && isempty(env.upper_samples) && error(\"Policy has no certified continuation\")
    key=RC.binary_key(p.encode(prev))
    budget=Inf
    if direction==:upper
        haskey(a.upper[t],key) || error(\"No certified policy budget for this incoming state\")
        budget=a.upper[t][key].value
    end
    # الگوها همهٔ تصمیم‌های صحیح را تثبیت می‌کنند؛ هر پاسخ با قید بودجه دوباره بررسی می‌شود.
    # ثانیه، مهلت هر تلاش است؛ زمان ساخت و مجموع تلاش‌ها نیز جدا ثبت می‌شود.
    patterns=direction==:upper ? get(a.responders[t],key,RC.IntegerPattern[]) : RC.IntegerPattern[]
    attempts=Union{Nothing,RC.IntegerPattern}[patterns...]
    if direction==:lower || response_order==:milp_first
        pushfirst!(attempts,nothing)
    elseif response_order==:portfolio_first
        push!(attempts,nothing)
    end
    records=NamedTuple[]
    last_bounds=(;lower=-Inf,upper=Inf,feasible=false,status=MOI.OPTIMIZE_NOT_CALLED)
    for (number,pattern) in enumerate(attempts)
        tick=time()
        # Add an explicit scenario-specific recourse block for previously
        # witnessed infeasible final-stage scenarios. Do not pass this keyword
        # to generic planning problems when no witnesses exist.
        m,extract=isempty(recourse_witnesses) ?
            p.build(t,prev,u;direction,env...,seconds) :
            p.build(t,prev,u;direction,env...,seconds,recourse_witnesses)
        add_exact_feasibility_nogoods!(m,forbidden_state_bits)
        isfinite(budget) && @constraint(m,objective_function(m)<=budget+1e-7*max(1.,abs(budget)))
        method=pattern===nothing ? :milp : :portfolio_lp
        if pattern!==nothing
            # ناسازگاری چینش الگو خطای پیاده‌سازی است؛ پنهان یا به جواب ممکن تبدیل نمی‌شود.
            RC.fix_pattern!(m,pattern)
            any(v->is_binary(v)||is_integer(v),all_variables(m)) && error(\"Portfolio response is not an LP\")
        end
        RC.solve_tracked!(m;context=\"decision t=\$t \$direction \$method\")
        bounds=RC.min_bounds(m);last_bounds=bounds
        budget_ok=(!isfinite(budget) ||
            bounds.upper<=budget+1e-7*max(1.,abs(budget)))
        accepted=forward_optimality_gate(bounds.status,bounds.feasible,budget_ok;
            require_optimal)
        codebook_restricted=(direction==:upper && t<p.horizon)
        possible_codebook_infeasibility=(codebook_restricted &&
            bounds.status in (MOI.INFEASIBLE,MOI.INFEASIBLE_OR_UNBOUNDED))
        push!(records,(;attempt=number,method=string(method),status=string(bounds.status),
            feasible=bounds.feasible,optimal=(bounds.status==MOI.OPTIMAL),
            accepted,budget_ok,possible_codebook_infeasibility,seconds=time()-tick))
        if accepted
            # Audited strict decision path must pass the original optimality check.
            require_optimal && require_optimal!(m;context=\"forward t=\$t \$method\")
            answer=extract(capture)
            return (;feasible=true,bounds,answer...,method,seconds=time()-started,attempts=records)
        end
    end
    # A restricted Upper Approximation's INFEASIBLE status is NOT a proof
    # of physical recourse infeasibility: its certified codebook may be too small.
    codebook_ambiguous=(direction==:upper && t<p.horizon &&
        last_bounds.status in (MOI.INFEASIBLE,MOI.INFEASIBLE_OR_UNBOUNDED))
    failure_reason=codebook_ambiguous ? :upper_codebook_or_physical_infeasible :
        (last_bounds.feasible && require_optimal ? :forward_no_optimality_certificate :
         :forward_no_feasible_incumbent)
    return (;feasible=false,bounds=last_bounds,state=nothing,immediate=Inf,operations=Dict(),
        method=:failed,failure_reason,seconds=time()-started,attempts=records)
end

# رفت‌وبرگشت با حفظ کران‌های معتبر ریشه؛ هزینهٔ یک مسیر جایگزین UB مقاوم نمی‌شود.
function run_improved_rddp(p::PlanningProblem;iterations=30,seconds=600.,ccg_iters=100,
        cut_iters=60,rtol=0.001,output_dir=nothing,capture=true,
        max_feasibility_repairs::Int=0,repair_mode::Symbol=:nogood,
        require_optimal::Bool=true)
    p.horizon>=1 && iterations>0 && seconds>0 && 0<=rtol<1 &&
        max_feasibility_repairs>=0 && repair_mode in (:nogood,:witness) ||
        error(\"Invalid planning settings or feasibility repair mode\")
    a=PlanningArchive(p.horizon)
    history=NamedTuple[];phase_log=NamedTuple[];last_path=NamedTuple[]
    lower=-Inf;upper=Inf;best_policy=nothing;reason=:iteration_limit
    started=time();trace_start=length(RC.SOLVER_TRACE)+1
    # Persist fully encoded Stage-2 states ruled out by a certified infeasible
    # Stage-3 fixed-scenario MILP. No hard-coded site choices.
    forbidden_stage2=Vector{Vector{Int}}()
    # Each item is a complete scenario in Phi_3 for which some Stage-2 state
    # was certified to have no Stage-3 feasible recourse.
    # This is a diagnostic scenario-discovery store, not a robust certificate.
    recourse_witnesses=Dict{String,Any}[]
    repair_used=false
    for iteration in 1:iterations
        path=NamedTuple[];prev=deepcopy(p.initial)
        restart_forward=false
        # گذر جلو: در دسترس بودن پوش بالا، غربال سناریوی بدترین آن را ممکن می‌کند.
        for t in 1:p.horizon
            screened=planning_oracle(p,a,t,prev,:upper;seconds,max_iters=ccg_iters,rtol)
            if screened.scenario===nothing || screened.infeasible
                screened=planning_oracle(p,a,t,prev,:lower;seconds,max_iters=ccg_iters,rtol)
            end
            push!(phase_log,(;iteration,phase=\"forward\",stage=t,reason=string(screened.reason),
                lower=screened.lower,upper=screened.upper,role=string(screened.bound_role)))
            screened.scenario===nothing && (reason=:no_forward_scenario;break)
            if t==2 && repair_mode==:witness && !isempty(recourse_witnesses)
                push!(phase_log,(;iteration,phase=\"witness_recourse_build\",stage=2,
                    reason=\"enforcing \$(length(recourse_witnesses)) Stage-3 feasibility witness(es)\",
                    lower=-Inf,upper=Inf,role=\"forward_witness_feasibility_only\"))
            end
            decision=planning_decision(p,a,t,prev,screened.scenario;seconds,capture,
                forbidden_state_bits=(t==2 && repair_mode==:nogood ?
                    forbidden_stage2 : Vector{Int}[]),
                recourse_witnesses=(t==2 && repair_mode==:witness ?
                    recourse_witnesses : Dict{String,Any}[]),require_optimal)
            if !decision.feasible
                # A fixed-scenario final-stage INFEASIBLE is a valid witness that
                # the exact predecessor state lacks complete recourse under
                # that realization. Never cut on TIME_LIMIT/no incumbent.
                if p.horizon==3 && t==3 && length(path)==2 &&
                    decision.bounds.status==MOI.INFEASIBLE
                    if repair_mode==:witness &&
                        length(recourse_witnesses)<max_feasibility_repairs
                        witness=deepcopy(screened.scenario)
                        p.validate(3,witness)
                        if !any(old->isequal(old,witness),recourse_witnesses)
                            push!(recourse_witnesses,witness)
                            repair_used=true
                            # Invalidate BEFORE restarting, not after another
                            # oracle or a root upper-bound claim can reuse it.
                            upper=Inf;best_policy=nothing
                            invalidate_upper_after_repair!(a)
                            restart_forward=true
                            reason=:feasibility_repair_retry
                            push!(phase_log,(;iteration,phase=\"feasibility_repair\",stage=2,
                                reason=\"embed certified-infeasible Stage-3 scenario as Stage-2 recourse\",
                                lower=-Inf,upper=Inf,role=\"forward_witness_feasibility_only\"))
                            break
                        end
                    elseif repair_mode==:nogood &&
                        length(forbidden_stage2)<max_feasibility_repairs
                        candidate=p.encode(path[end].decision.state)
                        if !any(bits->bits==candidate,forbidden_stage2)
                            push!(forbidden_stage2,candidate)
                            repair_used=true
                            upper=Inf;best_policy=nothing
                            invalidate_upper_after_repair!(a)
                            restart_forward=true
                            reason=:feasibility_repair_retry
                            push!(phase_log,(;iteration,phase=\"feasibility_repair\",stage=2,
                                reason=\"exclude exact state with certified infeasible Stage-3 witness\",
                                lower=-Inf,upper=Inf,role=\"forward_feasibility_only\"))
                            break
                        end
                    end
                end
                # Infeasibility and lack of an incumbent remain distinct.
                reason=(repair_mode==:witness && t==2 && !isempty(recourse_witnesses) &&
                    decision.bounds.status==MOI.INFEASIBLE) ?
                    :stage2_no_feasible_witness_recourse :
                    (decision.bounds.status==MOI.INFEASIBLE ?
                        :lower_recourse_infeasible :
                        (decision.bounds.feasible && require_optimal ?
                            :forward_no_optimality_certificate : :decision_no_incumbent))
                break
            end
            push!(path,(;stage=t,previous=deepcopy(prev),uncertainty=deepcopy(screened.scenario),decision))
            prev=decision.state
        end
        last_path=path
        restart_forward && continue
        length(path)==p.horizon || break
        # گذر عقب: ابتدا گواه بالایی، سپس برش پایین با نسخه‌های دودویی کامل حالت قبلی.
        for t in p.horizon:-1:2
            step=path[t];prev=step.previous
            r=repair_used || !require_optimal ?
                unavailable_upper(p,t,:uncertified_after_forward_repair) :
                planning_oracle(p,a,t,prev,:upper;seconds,max_iters=ccg_iters,rtol)
            !repair_used && require_optimal &&
                archive_upper!(a,t,p.encode(prev),r,p.scope(t))
            witness=r.scenario===nothing ? step.uncertainty : r.scenario
            p.validate(t,witness)
            c=p.cut(t,prev,witness;lower_cuts=a.cuts[t+1],seconds,max_iters=cut_iters,rtol=min(1e-6,rtol/10))
            c.scope==p.scope(t) || error(\"Lagrangian cut target mismatch\")
            length(c.slope)==length(p.encode(prev)) || error(\"Cut state layout mismatch\")
            push!(a.cuts[t],c)
            push!(phase_log,(;iteration,phase=\"backward\",stage=t,reason=string(r.reason),
                lower=r.lower,upper=r.upper,role=string(r.bound_role)))
        end
        # پایین و بالای ریشه هر دو با هزینهٔ تنزیل‌شدهٔ کل افق مرتبط‌اند.
        lo=planning_oracle(p,a,1,p.initial,:lower;seconds,max_iters=ccg_iters,rtol)
        # A repaired / diagnostic Forward path has no global robust UB.
        hi=repair_used || !require_optimal ?
            unavailable_upper(p,1,:uncertified_after_forward_repair) :
            planning_oracle(p,a,1,p.initial,:upper;seconds,max_iters=ccg_iters,rtol)
        lo.scope==hi.scope || error(\"Root targets differ\")
        lower=max(lower,lo.lower)
        if !repair_used && require_optimal
            archive_upper!(a,1,p.encode(p.initial),hi,p.scope(1))
            if hi.upper<upper && !hi.infeasible
                upper=hi.upper
                best_policy=deepcopy(a)
            end
        else
            upper=Inf;best_policy=nothing
        end
        isfinite(lower) && isfinite(upper) && lower>upper+1e-6*max(1.,abs(lower),abs(upper)) &&
            error(\"Global horizon bounds cross\")
        # No-good cuts were integrated into forward decisions only; robust
        # C&CG oracle and backward value-function certificates still require
        # a complete feasibility-cut implementation. Do not mislabel this as
        # a global proof of robust convergence or a certified policy upper.
        if repair_used || !require_optimal
            upper=Inf
            best_policy=nothing
        end
        if length(path)==p.horizon && !isfinite(upper)
            # A successful forward path is not a robust proof.
            reason=require_optimal ? :forward_path_found_no_robust_certificate :
                :diagnostic_forward_only
        end
        # No global backward feasibility cuts yet. Never certify global UB or convergence.
        # Retain the algorithm's local experimental upper only in phase/solver traces.
        upper=Inf;best_policy=nothing;reason=:backward_feasibility_uncertified
        gap=Inf
        push!(history,(;iteration,lower,upper,gap,seconds=time()-started,
            cuts=sum(length,a.cuts),samples=sum(length,a.upper)))
        println(\"RDDP iteration=\$iteration LB=\$lower UB=\$upper gap=\$gap\")
        result=(;archive=a,best_policy,history,phase_log,path=last_path,lower,upper,
            converged=gap<=rtol,reason=gap<=rtol ? :gap : reason,scope=p.scope(1),
            solver_trace=copy(RC.SOLVER_TRACE[trace_start:end]))
        output_dir===nothing || write_planning_outputs(output_dir,p,result)
        gap<=rtol && return result
    end
    repair_used && reason==:feasibility_repair_retry &&
        (reason=:feasibility_repair_iteration_limit)
    result=(;archive=a,best_policy,history,phase_log,path=last_path,lower,upper,
        converged=false,reason,scope=p.scope(1),solver_trace=copy(RC.SOLVER_TRACE[trace_start:end]))
    output_dir===nothing || write_planning_outputs(output_dir,p,result)
    return result
end

# بازسازی حالت از بیت‌های حل‌شده، گردکردن ظرفیت خارج از شبکه نیست.
function solved_state(v,grids)
    raw=value.(v[\"state_bits\"])
    maximum(abs.(raw.-round.(raw));init=0.)<=1e-5 || error(\"Nonintegral state incumbent\")
    values=Dict(k=>zeros(num_roads) for k in (\"z\",\"Cc\",\"Ce\",\"Cv\"))
    for (x,l) in zip(round.(Int,raw),v[\"state_layout\"])
        values[l.key][l.road]+=x*l.weight
    end
    for key in (\"z\",\"Cc\",\"Ce\",\"Cv\"),a in A_set
        abs(value(v[key][a])-values[key][a])<=1e-5*max(1.,abs(values[key][a])) || error(\"Physical state and bits disagree\")
    end
    return StageState(values[\"z\"],values[\"Cc\"],values[\"Ce\"],values[\"Cv\"])
end
# The already-defined discounted physical objective contribution of a stage;
# excluding its cost-to-go variable is essential when attaching witnesses.
function discounted_stage_physical_cost(t::Int,v)
    t in T_set || error(\"Invalid stage for physical cost\")
    return (v[\"Inv_Cost\"]+v[\"Ope_Cost_Total\"])/(1.0+g7cfg().sigma)^(t-1)
end

# Independent post-solve numerical checks. The structural JUMP feasibility checker is
# NOT a replacement for independently deriving the physical equations below.
const G7_STAGE_AUDIT_ROWS = NamedTuple[]
function audit_stage_solution!(m,v,t;tol=1e-5)
    has_values(m) && primal_status(m)==MOI.FEASIBLE_POINT || error(\"No feasible stage incumbent for physical audit\")
    c=g7cfg()
    failures=NamedTuple[]
    worst=Dict{String,Float64}()
    g7val(x)=x isa Number ? Float64(x) : Float64(value(x))
    function chk(label,lhs,rhs;scale=1.0)
        x=Float64(lhs);y=Float64(rhs)
        d=abs(x-y);limit=tol*max(1.0,abs(x),abs(y),Float64(scale))
        worst[label]=max(get(worst,label,0.0),d)
        if !isfinite(d) || d>limit
            push!(failures,(;stage=t,label,actual=x,expected=y,residual=d,limit))
        end
    end
    function leq(label,x,cap)
        a=Float64(x);b=Float64(cap)
        d=max(0.0,a-b);limit=tol*max(1.0,abs(a),abs(b))
        worst[label]=max(get(worst,label,0.0),d)
        if !isfinite(d) || d>limit
            push!(failures,(;stage=t,label,actual=a,expected=b,residual=d,limit))
        end
    end
    for a in A_set
        zi=value(v[\"z\"][a]);ph=value(v[\"phi_inv\"][a]);old=v[\"z_prev\"][a]
        for key in (\"z\",\"phi_inv\",\"y_fc\",\"y_es\",\"y_pv\")
            bi=value(v[key][a]);leq(\"BINARY_\"*key,abs(bi-round(bi)),0.0)
        end
        chk(\"EQ37\",ph,zi-g7val(old))
        leq(\"EQ38\",g7val(old),zi)
        for (key,ex,yn,base) in ((\"Cc\",\"Ec\",\"y_fc\",Cc_0),
                (\"Ce\",\"Ee\",\"y_es\",Ce_0),(\"Cv\",\"Ev\",\"y_pv\",Cv_0))
            chk(\"EQ41_43_\"*key,value(v[key][a]),g7val(v[key*\"_prev\"][a])+ph*base+value(v[ex][a]))
            leq(\"EQ44_\"*key,value(v[ex][a]),
                (key==\"Cc\" ? Ec_max : key==\"Ce\" ? Ee_max : Ev_max)*value(v[yn][a]))
            chk(\"PRODUCT_\"*key,value(v[\"y\"*ex][a]),value(v[yn][a])*value(v[ex][a]))
        end
        leq(\"EQ39_FC\",value(v[\"y_fc\"][a]),zi)
        leq(\"EQ40_FC\",value(v[\"y_fc\"][a])+ph,1.0)
        leq(\"EQ39_ES\",value(v[\"y_es\"][a]),zi)
        leq(\"EQ40_ES\",value(v[\"y_es\"][a])+ph,1.0)
        leq(\"EQ39_PV\",value(v[\"y_pv\"][a]),zi)
        leq(\"EQ40_PV\",value(v[\"y_pv\"][a])+ph,1.0)
        Ce=value(v[\"Ce\"][a])
        for tau in Tau_set
            ec=value(v[\"Pe_Ec\"][a,tau]);ed=value(v[\"Pe_Ed\"][a,tau])
            qc=value(v[\"Qe_Ec\"][a,tau]);qd=value(v[\"Qe_Ed\"][a,tau])
            vc=value(v[\"v_Ec\"][a,tau]);vd=value(v[\"v_Ed\"][a,tau])
            leq(\"BINARY_v_Ec\",abs(vc-round(vc)),0.0)
            leq(\"BINARY_v_Ed\",abs(vd-round(vd)),0.0)
            leq(\"EQ19_EXCLUSIVE\",vc+vd,zi)
            for (P,Q,bit) in ((ec,qc,vc),(ed,qd,vd))
                if c.bess_power_policy==:fixed_20kw
                    leq(\"EQ19_BESS_FIXED\",P,Pe_max*bit)
                    leq(\"EQ19_BESS_QFIXED\",Q,Pe_max*q_fac_bound*bit)
                else
                    leq(\"EQ19_BESS_SCALED\",P,Pe_ramp_rate*Ce)
                    leq(\"EQ19_BESS_SWITCH\",P,Pe_ramp_rate*Ce_max*bit)
                    leq(\"EQ19_BESS_QSCALED\",Q,Pe_ramp_rate*q_fac_bound*Ce)
                    leq(\"EQ19_BESS_QSWITCH\",Q,Pe_ramp_rate*q_fac_bound*Ce_max*bit)
                end
            end
            chk(\"EQ25\",value(v[\"Pn\"][a,tau]),value(v[\"Pcs\"][a,tau])+ec-ed-value(v[\"Rv\"][a,tau]))
            chk(\"EQ32\",value(v[\"Pcs\"][a,tau]),c.delta_p*value(v[\"f_pcs\"][a,tau]))
            leq(\"EQ24\",value(v[\"Rv\"][a,tau]),value(v[\"Av\"][a,tau]))
            chk(\"EQ24_STATION_PV_AVAIL\",value(v[\"Av\"][a,tau]),
                value(v[\"Cv\"][a])*g7val(v[\"zeta_station_pv_profile\"][a,tau]))
            chk(\"EQ24_STATION_PV_CURTAIL\",value(v[\"Rv\"][a,tau])+value(v[\"Rv_curtail\"][a,tau]),
                value(v[\"Av\"][a,tau]))
            if CHARGING_ASSIGNMENT_MODE==:paper_exact
                leq(\"EQ35\",value(v[\"f_pcs\"][a,tau]),
                    sum(X_rska[rs,k,a]*value(v[\"f_rs_ch\"][rs,k,tau]) for rs in OD_set,k in K_set))
            end
            if c.capacity_mode==:printed_eq33
                leq(\"EQ33\",value(v[\"Pcs\"][a,tau]),g7val(v[\"Cc_prev\"][a])+value(v[\"Ec\"][a]))
            else
                leq(\"EQ33_INSTALLED\",value(v[\"Pcs\"][a,tau]),value(v[\"Cc\"][a]))
            end
            energy=value(v[\"E_stored\"][a,tau]);delta=eta_ch*ec-ed/eta_dis
            leq(\"EQ20_SOC_UPPER\",energy,c.soc_max*Ce)
            leq(\"EQ20_SOC_LOWER\",c.soc_min*Ce,energy)
            day=div(tau-1,24)+1;is_start=(tau-1)%24==0;is_end=tau%24==0
            if c.soc_boundary==:cyclic_free_e0
                e0=value(v[\"E0\"][a,day])
                chk(\"EQ20_RECURSION\",energy,(is_start ? e0 : value(v[\"E_stored\"][a,tau-1]))+delta)
                is_end && chk(\"EQ20_CYCLIC\",energy,e0)
            elseif c.soc_boundary==:fractions
                chk(\"EQ20_RECURSION\",energy,(is_start ? c.soc_initial*Ce : value(v[\"E_stored\"][a,tau-1]))+delta)
                is_end && chk(\"EQ20_TERMINAL\",energy,c.soc_terminal*Ce)
            else
                chk(\"EQ20_RECURSION\",energy,(tau==1 ? c.soc_initial*Ce : value(v[\"E_stored\"][a,tau-1]))+delta)
                tau==num_tau && chk(\"EQ20_TERMINAL\",energy,c.soc_terminal*Ce)
            end
        end
    end
    for tau in Tau_set
        for rs in OD_set
            demand=Df_initial[tau,rs]*(1.0+g7val(v[\"theta_t\"]))
            chk(\"UTN_OD_CH\",sum(value(v[\"f_rs_ch\"][rs,k,tau]) for k in K_set),
                gamma_factor*demand)
            chk(\"UTN_OD_UN\",sum(value(v[\"f_rs_un\"][rs,k,tau]) for k in K_set),
                (1.0-gamma_factor)*demand)
            for k in K_set
                leq(\"UTN_DUAL_CH\",value(v[\"phi_od_ch\"][rs,tau]),
                    sum(Lambda_rskb[rs,k,b]*value(v[\"mu_b_ch\"][b,tau]) for b in B_set))
                leq(\"UTN_DUAL_UN\",value(v[\"phi_od_un\"][rs,tau]),
                    sum(Lambda_rskb[rs,k,b]*value(v[\"mu_b_un\"][b,tau]) for b in B_set))
            end
        end
        for b in B_set
            xch=value(v[\"x_ch\"][b,tau]);xun=value(v[\"x_un\"][b,tau])
            chk(\"UTN_ROAD_CH\",xch,
                sum(Lambda_rskb[rs,k,b]*value(v[\"f_rs_ch\"][rs,k,tau]) for rs in OD_set,k in K_set))
            chk(\"UTN_ROAD_UN\",xun,
                sum(Lambda_rskb[rs,k,b]*value(v[\"f_rs_un\"][rs,k,tau]) for rs in OD_set,k in K_set))
            chk(\"UTN_TOTAL\",value(v[\"x_total\"][b,tau]),xch+xun)
            leq(\"UTN_ROAD_CAPACITY\",value(v[\"x_total\"][b,tau]),phi_b[b])
            chk(\"UTN_DUAL_LAMBDA\",value(v[\"lambda_b\"][b,tau]),value(v[\"h_del\"][b,tau]))
            chk(\"UTN_DUAL_MU_CH\",value(v[\"mu_b_ch\"][b,tau])-value(v[\"lambda_b\"][b,tau]),h0_b[b])
            chk(\"UTN_DUAL_MU_UN\",value(v[\"mu_b_un\"][b,tau])-value(v[\"lambda_b\"][b,tau]),h0_b[b])
        end
        for w in eachindex(wt_buses)
            pw=value(v[\"Pwt\"][w,tau]);qw=value(v[\"Qwt\"][w,tau])
            chk(\"EQ21_WT\",pw+value(v[\"Pwt_curtail\"][w,tau]),
                (1.0+g7val(v[\"zeta_t\"]))*wt_capacities[w]*g7val(v[\"xi_wt_profile\"][w,tau]))
            chk(\"EQ22_WT\",qw,pw*tan_phi)
            leq(\"EQ23_WT\",pw*sqrt(1.0+tan_phi^2),Sw_max)
        end
        for w in eachindex(pv_pdn_buses)
            pp=value(v[\"Ppv_pdn\"][w,tau]);qp=value(v[\"Qpv_pdn\"][w,tau])
            chk(\"EQ21_PV\",pp+value(v[\"Ppv_pdn_curtail\"][w,tau]),
                (1.0+g7val(v[\"zeta_t\"]))*pv_pdn_capacities[w]*g7val(v[\"zeta_pv_profile\"][w,tau]))
            chk(\"EQ22_PV\",qp,pp*tan_phi)
            leq(\"EQ23_PV\",pp*sqrt(1.0+tan_phi^2),Sw_max)
        end
        chk(\"EQ34\",sum(value(v[\"f_pcs\"][a,tau]) for a in A_set),
            gamma_factor*sum(Df_initial[tau,:])*(1.0+g7val(v[\"theta_t\"])))
        if CHARGING_ASSIGNMENT_MODE==:paper_exact
            for rs in OD_set,k in K_set
                leq(\"EQ36\",value(v[\"f_rs_ch\"][rs,k,tau]),
                    sum(X_rska[rs,k,a]*value(v[\"f_pcs\"][a,tau]) for a in A_set))
            end
        end
        chk(\"EQ27_SLACK\",value(v[\"V_bus\"][1,tau]),V_slack)
        leq(\"EQ18_ACTIVE\",value(v[\"Pb_u\"][tau]),Pb_max)
        leq(\"EQ18_REACTIVE\",value(v[\"Qb_u\"][tau]),Qb_max)
        for i in I_set
            vb=value(v[\"V_bus\"][i,tau]);leq(\"EQ27_V_MAX\",vb,V_max);leq(\"EQ27_V_MIN\",V_min,vb)
            pin=(i==1 ? value(v[\"Pb_u\"][tau]) : 0.0)+
                sum((value(v[\"Pf\"][l,tau]) for l in L_set if to_bus[l]==i); init=0.0)+
                sum((value(v[\"Pwt\"][w,tau]) for w in eachindex(wt_buses) if wt_buses[w]==i); init=0.0)+
                sum((value(v[\"Ppv_pdn\"][w,tau]) for w in eachindex(pv_pdn_buses) if pv_pdn_buses[w]==i); init=0.0)+
                value(v[\"delta_p_plus\"][i,tau])-value(v[\"delta_p_minus\"][i,tau])
            pout=sum((value(v[\"Pf\"][l,tau]) for l in L_set if from_bus[l]==i); init=0.0)+PD_bus_96[tau]+
                sum((value(v[\"Pn\"][a,tau]) for a in A_set if candidate_road_to_bus[a]==i); init=0.0)
            chk(\"EQ28_P\",pin,pout)
            qin=(i==1 ? value(v[\"Qb_u\"][tau]) : 0.0)+
                sum((value(v[\"Qf\"][l,tau]) for l in L_set if to_bus[l]==i); init=0.0)+
                sum((value(v[\"Qwt\"][w,tau]) for w in eachindex(wt_buses) if wt_buses[w]==i); init=0.0)+
                sum((value(v[\"Qpv_pdn\"][w,tau]) for w in eachindex(pv_pdn_buses) if pv_pdn_buses[w]==i); init=0.0)
            qout=sum((value(v[\"Qf\"][l,tau]) for l in L_set if from_bus[l]==i); init=0.0)+
                value(v[\"delta_q_plus\"][i,tau])-value(v[\"delta_q_minus\"][i,tau])+QD_bus_96[tau]+
                sum((value(v[\"Qe_Ec\"][a,tau])-value(v[\"Qe_Ed\"][a,tau]) for a in A_set if candidate_road_to_bus[a]==i); init=0.0)
            chk(\"EQ29_Q\",qin,qout)
        end
        for l in L_set
            P=value(v[\"Pf\"][l,tau]);Q=value(v[\"Qf\"][l,tau]);dV=value(v[\"dV_line\"][l,tau])
            leq(\"EQ30_P_POS\",P,Pf_max[l]);leq(\"EQ30_P_NEG\",-P,Pf_max[l])
            leq(\"EQ30_Q_POS\",Q,Qf_max[l]);leq(\"EQ30_Q_NEG\",-Q,Qf_max[l])
            leq(\"EQ27_DV_POS\",dV,V_bound_dV)
            leq(\"EQ27_DV_NEG\",-dV,V_bound_dV)
            if c.topology.status[l]==0
                chk(\"OPEN_PF\",P,0.0);chk(\"OPEN_QF\",Q,0.0)
            else
                chk(\"EQ26_DV_ZERO\",dV,0.0)
                chk(\"EQ26\",value(v[\"V_bus\"][from_bus[l],tau]),
                    value(v[\"V_bus\"][to_bus[l],tau])+
                    (R_line[l]*P+X_line[l]*Q)/(1000.0*c.voltage_base_kv^2*V_slack))
            end
        end
    end
    eq17_lhs=sum(gamma_factor*value(v[\"phi_od_ch\"][rs,tau])*Df_initial[tau,rs]*(1.0+g7val(v[\"theta_t\"]))+
        (1.0-gamma_factor)*value(v[\"phi_od_un\"][rs,tau])*Df_initial[tau,rs]*(1.0+g7val(v[\"theta_t\"]))
        for tau in Tau_set,rs in OD_set)
    eq17_rhs=sum(h0_b[b]*(value(v[\"x_ch\"][b,tau])+value(v[\"x_un\"][b,tau]))+
        phi_b[b]*value(v[\"lambda_b\"][b,tau]) for tau in Tau_set,b in B_set)
    chk(\"EQ17_STRONG_DUALITY\",eq17_lhs,eq17_rhs)
    if !isempty(failures)
        firstfail=first(failures)
        error(\"Gate7 independent stage audit FAILED for stage=\$t: \"*repr(firstfail)*\"; failure_count=\"*string(length(failures)))
    end
    for (label,d) in sort(collect(worst);by=x->x[1])
        push!(G7_STAGE_AUDIT_ROWS,(;stage=t,equation=label,max_residual=d,status=\"PASS_INDEPENDENT_SUBSET\"))
    end
    return (;stage=t,checked=length(worst),worst=maximum(values(worst)),status=\"PASS_INDEPENDENT_SUBSET\")
end

function physical_problem(grids;initial_state_name::String,
        initial_station_state::AbstractVector{<:Real},
        capacity_mode=CHARGING_CAPACITY_MODE,optimizer=nothing)
    initial_state_name in INITIAL_STATE_SCENARIOS || error(\"Unrecognized initial-state branch\")
    initial_state_name==g7cfg().initial_state || error(\"Initial state differs from CLI scenario\")
    capacity_mode==g7cfg().capacity_mode || error(\"Capacity policy differs from CLI\")
    length(initial_station_state)==num_roads || error(\"Initial station-state length mismatch\")
    all(x -> x in (0,1), initial_station_state) || error(\"Initial station state must be binary\")
    Int.(initial_station_state)==initial_station_vector(initial_state_name) ||
        error(\"Initial station vector does not match its declared branch\")
    z0=Float64.(initial_station_state)
    initial=StageState(z0,z0.*Cc_0,z0.*Ce_0,z0.*Cv_0)
    build=function(t,prev,u;recourse_witnesses::Vector{Dict{String,Any}}=Dict{String,Any}[],kwargs...)
        m,v=build_certified_stage(t,prev,u,grids;capacity_mode,initial_station_state,kwargs...)
        if !isempty(recourse_witnesses)
            t==2 || error(\"Witness-embedded recourse is only supported at Stage 2\")
            length(recourse_witnesses)<=3 ||
                error(\"At most three witness recourse blocks supported; this is diagnostic\")
            stage2_objective=objective_function(m)
            stage2_sense=objective_sense(m)
            time_budget=haskey(kwargs,:seconds) ? Float64(kwargs[:seconds]) : EVAL_TIME_LIMIT
            for w in recourse_witnesses
                validate_scenario(3,w)
                # Append the COMPLETE Stage-3 feasibility model linked to the
                # *decision variables* of Stage 2, not a fixed hand-picked state.
                # This is a valid necessary condition for robust recourse:
                # recourse may adapt independently for each observed Stage-3 witness.
                _,vw=build_stage_subproblem(3,v[\"z\"],v[\"Cc\"],v[\"Ce\"],v[\"Cv\"],w;
                    time_limit_sec=time_budget,capacity_mode,initial_station_state,shared_model=m)
                state_bits!(m,vw,grids)
                fix(vw[\"alpha_cost_to_go\"],0.0;force=true)
                # Cost-linked scenario recourse (finite-witness lower envelope):
                # Stage-2 alpha already appears once in its own objective.
                # Enforce alpha >= discounted Stage-3 operating/investment cost
                # for each witnessed scenario, in addition to feasibility.
                # Each scenario retains independent stage-3 adaptive decisions.
                witness_cost = discounted_stage_physical_cost(3, vw)
                @constraint(m, v[\"alpha_cost_to_go\"] >= witness_cost)
            end
            # Shared builder overwrote the objective with the last witness;
            # restore Stage-2 objective (which already includes alpha).
            set_objective_function(m,stage2_objective)
            set_objective_sense(m,stage2_sense)
        end
        # Shared-model construction unregisters JuMP names; register only after
        # recourse blocks have all been attached.
        m[:revcs_output_state_bits] = v[\"state_bits\"]
        extract=function(capture)
            audit_stage_solution!(m,v,t)
            operations=Dict{String,Any}()
            if capture
                for key in (\"Pcs\",\"Pb_u\",\"Qb_u\",\"Pwt\",\"Ppv_pdn\",\"Rv\",\"Rv_curtail\",\"Pe_Ec\",
                        \"Pe_Ed\",\"E_stored\",\"Pn\",\"V_bus\",\"Pf\",\"Qf\",\"x_ch\",\"x_un\",\"x_total\",
                        \"delta_p_plus\",\"delta_p_minus\",\"delta_q_plus\",\"delta_q_minus\",
                        \"Pwt_curtail\",\"Ppv_pdn_curtail\",\"f_pcs\")
                    operations[key]=Array(value.(v[key]))
                end
            end
            return (;state=solved_state(v,grids),immediate=objective_value(m)-value(v[\"alpha_cost_to_go\"]),operations)
        end
        return m,extract
    end
    return PlanningProblem(num_periods,initial,s->encode_state(s,grids),
        t->physical_cost_scope(t,grids;capacity_mode,initial_station_state),
        (t,prev;kwargs...)->solve_native_stage(t,prev,grids;capacity_mode,optimizer,initial_station_state,kwargs...),build,
        (t,prev,u;kwargs...)->certified_lagrangian_cut(t,prev,u,grids;capacity_mode,initial_station_state,kwargs...),validate_scenario,b->decode_state(b,grids))
end

# فایل روی دیسک فقط پیشنهاد حالت است؛ رشتهٔ scope یا هزینهٔ داخل آن گواه معتبر نیست.
struct UnverifiedPolicyImport
    horizon::Int
    candidates::Vector{Vector{Vector{Int}}}
    source_scope::String
    ignored_cuts::Int
end
function archive_document(p::PlanningProblem,a::PlanningArchive)
    stages=Dict{String,Any}()
    for t in 1:p.horizon+1
        stages[string(t)]=Dict(\"cuts\"=>[Dict(\"intercept\"=>c.intercept,\"slope\"=>c.slope,
            \"anchor_lower\"=>c.anchor_lower,\"anchor_upper\"=>c.anchor_upper,
            \"converged\"=>c.converged,\"scope\"=>c.scope) for c in a.cuts[t]],
            \"samples\"=>[Dict(\"bits\"=>s.bits,\"value\"=>s.value,\"scope\"=>s.scope)
                for s in sort!(collect(values(a.upper[t]));by=s->RC.binary_key(s.bits))])
    end
    return merge(Dict{String,Any}(\"schema\"=>\"REVCS19-gate7-policy-v1\",\"trust_on_load\"=>\"unverified_import\",
        \"root_scope\"=>p.scope(1),\"horizon\"=>p.horizon,\"stages\"=>stages),g7_scope_metadata())
end
function save_policy(path,p::PlanningProblem,a::PlanningArchive)
    open(path,\"w\") do io;TOML.print(io,archive_document(p,a));end
end
function load_policy(path,p::PlanningProblem)
    doc=TOML.parsefile(path)
    doc[\"schema\"] in (\"REVCS19-gate7-policy-v1\",\"REVCS18-policy-v2\",\"REVCS17-policy-v2\",\"REVCS16-policy-v1\") || error(\"Unknown archive schema\")
    doc[\"horizon\"]==p.horizon || error(\"Policy horizon mismatch\")
    # حتی فایل دارای هش یکسان، نمونه و برش قابل استفاده تولید نمی‌کند.
    candidates=[Vector{Int}[] for _ in 1:p.horizon]
    n=length(p.encode(p.initial));ignored=0
    for t in 1:p.horizon
        stage=doc[\"stages\"][string(t)]
        ignored+=length(get(stage,\"cuts\",[]))
        for d in stage[\"samples\"]
            b=d[\"bits\"]
            length(b)==n && all(v->v isa Integer && v in (0,1),b) || error(\"Invalid imported state code\")
            bits=Int.(b)
            # decode، کدهای استفاده‌نشدهٔ ظرفیت و ناسازگاری حالت را نیز رد می‌کند.
            p.encode(p.decode(bits))==bits || error(\"Imported state does not round-trip\")
            bits in candidates[t] || push!(candidates[t],bits)
        end
    end
    return UnverifiedPolicyImport(p.horizon,candidates,string(doc[\"root_scope\"]),ignored)
end
function revalidate_policy(p::PlanningProblem,imported::UnverifiedPolicyImport;
        seconds=600.,ccg_iters=100,rtol=0.001,output_dir=nothing)
    imported.horizon==p.horizon || error(\"Imported horizon mismatch\")
    a=PlanningArchive(p.horizon);records=NamedTuple[]
    # هزینه، برش، الگو و scope فایل واردشده نادیده گرفته می‌شوند؛ از انتهای افق حل تازه می‌شود.
    # برش‌های قدیمی بازاستفاده نمی‌شوند؛ آرشیو تازه برای پایین، کران صفر معتبر دارد.
    for t in p.horizon:-1:1
        bits=t==1 ? [p.encode(p.initial)] : imported.candidates[t]
        for b in bits
            prev=t==1 ? p.initial : p.decode(b)
            r=planning_oracle(p,a,t,prev,:upper;seconds,max_iters=ccg_iters,rtol)
            accepted=archive_upper!(a,t,b,r,p.scope(t))
            push!(records,(;stage=t,state=RC.binary_key(b),accepted,upper=r.upper,
                reason=string(r.reason),columns=length(r.columns)))
        end
    end
    key=RC.binary_key(p.encode(p.initial))
    verified=haskey(a.upper[1],key)
    upper=verified ? a.upper[1][key].value : Inf
    if output_dir!==nothing
        mkpath(output_dir);write_rows(joinpath(output_dir,\"revalidation.csv\"),records)
        verified && save_policy(joinpath(output_dir,\"revalidated_policy.toml\"),p,a)
    end
    return (;archive=a,verified,upper,records,discarded_cuts=imported.ignored_cuts)
end

csvcell(x)=\"\\\"\"*replace(string(x),'\"'=>\"\\\"\\\"\")*\"\\\"\"
function write_rows(path,rows)
    open(path,\"w\") do io
        isempty(rows) && return
        fields=propertynames(first(rows))
        println(io,join(string.(fields),\",\"))
        for r in rows;println(io,join((csvcell(getproperty(r,f)) for f in fields),\",\"));end
    end
end

# شکل همگرایی تنها از کران‌های متناهی محاسبه‌شده ساخته می‌شود؛ Inf به نقطهٔ عددی تبدیل نمی‌شود.
function convergence_svg(path,history)
    finite=[v for h in history for v in (h.lower,h.upper) if isfinite(v)]
    isempty(finite) && return
    lo,hi=extrema(finite);span=max(1.,hi-lo);n=max(1,length(history)-1)
    open(path,\"w\") do io
        println(io,\"<svg xmlns=\\\"http://www.w3.org/2000/svg\\\" width=\\\"800\\\" height=\\\"420\\\" viewBox=\\\"0 0 800 420\\\"><rect width=\\\"800\\\" height=\\\"420\\\" fill=\\\"white\\\"/><text x=\\\"50\\\" y=\\\"25\\\">Computed whole-horizon bounds (finite values only)</text>\")
        println(io,\"<path d=\\\"M50 45V370H760\\\" fill=\\\"none\\\" stroke=\\\"black\\\"/><text x=\\\"50\\\" y=\\\"410\\\">Iteration; blue = LB, red = UB</text>\")
        for (key,color) in ((:lower,\"blue\"),(:upper,\"red\"))
            points=String[]
            for (i,h) in enumerate(history)
                v=getproperty(h,key)
                isfinite(v) || continue
                x=50+710*(i-1)/n;y=370-310*(v-lo)/span
                push!(points,\"\$x,\$y\")
                println(io,\"<circle cx=\\\"\$x\\\" cy=\\\"\$y\\\" r=\\\"3\\\" fill=\\\"\$color\\\"><title>iteration \$(h.iteration): \$v</title></circle>\")
            end
            println(io,\"<polyline points=\\\"\$(join(points,\" \"))\\\" fill=\\\"none\\\" stroke=\\\"\$color\\\"/>\")
        end
        println(io,\"</svg>\")
    end
end
function write_planning_outputs(dir,p,r)
    mkpath(dir)
    write_rows(joinpath(dir,\"convergence.csv\"),r.history)
    write_rows(joinpath(dir,\"phases.csv\"),r.phase_log)
    write_rows(joinpath(dir,\"solver_trace.csv\"),r.solver_trace)
    save_policy(joinpath(dir,\"archive.toml\"),p,r.archive)
    save_solve_audit(joinpath(dir,\"REVCS19_G7_SOLVE_AUDIT.tsv\"))
    write_rows(joinpath(dir,\"REVCS19_G7_STAGE_AUDIT.csv\"),G7_STAGE_AUDIT_ROWS)
    policy_path=joinpath(dir,\"certified_policy.toml\")
    if r.best_policy===nothing
        isfile(policy_path) && rm(policy_path)
    else
        save_policy(policy_path,p,r.best_policy)
    end
    open(joinpath(dir,\"status.toml\"),\"w\") do io
        TOML.print(io,merge(Dict{String,Any}(\"lower\"=>r.lower,\"upper\"=>r.upper,
            \"converged\"=>r.converged,\"reason\"=>string(r.reason),\"scope\"=>r.scope,
            \"full_paper_reproduction\"=>false,
            \"upper_extension\"=>\"finite on certified sample codebook; +Inf elsewhere\"),
            g7_scope_metadata()))
    end
    state_rows=NamedTuple[];operation_rows=NamedTuple[];capacity_rows=NamedTuple[];uncertainty_rows=NamedTuple[]
    for step in r.path
        for (j,b) in enumerate(p.encode(step.decision.state))
            push!(state_rows,(;stage=step.stage,bit=j,value=b,immediate_cost=step.decision.immediate))
        end
        # ظرفیت‌ها و عدم‌قطعیت واقعی مسیر برای بازسازی نمودارهای سرمایه‌گذاری و بهره‌برداری صادر می‌شوند.
        if step.decision.state isa StageState
            st=step.decision.state;pr=step.previous
            for road in A_set
                push!(capacity_rows,(;stage=step.stage,road,z=st.z[road],new_station=st.z[road]-pr.z[road],
                    charging_kw=st.Cc[road],storage_kwh=st.Ce[road],pv_kw=st.Cv[road],
                    charging_expansion_kw=st.Cc[road]-pr.Cc[road]-(st.z[road]-pr.z[road])*Cc_0,
                    storage_expansion_kwh=st.Ce[road]-pr.Ce[road]-(st.z[road]-pr.z[road])*Ce_0,
                    pv_expansion_kw=st.Cv[road]-pr.Cv[road]-(st.z[road]-pr.z[road])*Cv_0))
            end
            u=step.uncertainty
            for key in (\"theta_t\",\"zeta_t\")
                push!(uncertainty_rows,(;stage=step.stage,variable=key,index=\"scalar\",value=Float64(u[key])))
            end
            for key in (\"xi_wt\",\"zeta_pv\",\"zeta_station_pv\"),idx in CartesianIndices(u[key])
                push!(uncertainty_rows,(;stage=step.stage,variable=key,index=join(Tuple(idx),\":\"),value=Float64(u[key][idx])))
            end
        end
        for (key,values) in step.decision.operations,idx in CartesianIndices(values)
            push!(operation_rows,(;stage=step.stage,variable=key,index=join(Tuple(idx),\":\"),value=values[idx]))
        end
    end
    write_rows(joinpath(dir,\"forward_states.csv\"),state_rows)
    write_rows(joinpath(dir,\"forward_dispatch.csv\"),operation_rows)
    write_rows(joinpath(dir,\"forward_capacities.csv\"),capacity_rows)
    write_rows(joinpath(dir,\"forward_uncertainty.csv\"),uncertainty_rows)
    convergence_svg(joinpath(dir,\"convergence.svg\"),r.history)
end

# ارزیابی مسیرهای صریح: شکست حذف نمی‌شود و زمان پاسخ هر مرحله ثبت می‌شود.
function evaluate_policy(p::PlanningProblem,a::PlanningArchive,paths;direction=:upper,
        seconds=600.,output_dir=nothing,response_order=:portfolio_first)
    frozen=deepcopy(a);rows=NamedTuple[];stage_rows=NamedTuple[]
    for (id,path) in enumerate(paths)
        length(path)==p.horizon || error(\"Evaluation path has wrong horizon\")
        prev=deepcopy(p.initial);total=0.;complete=true;status=\"complete\";started=time()
        for t in 1:p.horizon
            d=planning_decision(p,frozen,t,prev,path[t];direction,seconds,response_order)
            push!(stage_rows,(;path=id,stage=t,feasible=d.feasible,method=string(d.method),
                seconds=d.seconds,attempts=length(d.attempts),status=string(d.bounds.status)))
            if !d.feasible
                complete=false;status=string(d.bounds.status);break
            end
            total+=d.immediate;prev=d.state
        end
        push!(rows,(;path=id,complete,cost=complete ? total : Inf,status,seconds=time()-started))
    end
    costs=[r.cost for r in rows if r.complete];n=length(rows)
    summary=(;count=n,completed=length(costs),failed=n-length(costs),
        failure_rate=n==0 ? NaN : (n-length(costs))/n,
        conditional_mean=isempty(costs) ? NaN : mean(costs),
        unconditional_mean=n==0 ? NaN : (length(costs)==n ? mean(costs) : Inf),
        minimum=isempty(costs) ? NaN : minimum(costs),maximum=isempty(costs) ? NaN : maximum(costs),
        response_seconds=sum(r.seconds for r in stage_rows;init=0.),
        maximum_response_seconds=maximum((r.seconds for r in stage_rows);init=0.),
        portfolio_lp_successes=count(r->r.feasible&&r.method==\"portfolio_lp\",stage_rows),
        robust_upper_claim=false)
    if output_dir!==nothing
        mkpath(output_dir);write_rows(joinpath(output_dir,\"policy_evaluation.csv\"),rows)
        write_rows(joinpath(output_dir,\"policy_response_times.csv\"),stage_rows)
        open(joinpath(output_dir,\"evaluation_summary.toml\"),\"w\") do io
            TOML.print(io,Dict(string(k)=>v for (k,v) in pairs(summary)))
        end
    end
    return (;rows,stage_rows,summary)
end

# توزیع باید تابع ورودی کاربر باشد؛ بذر صریح بازتولید نمونه‌ها را ممکن می‌کند.
# این رابط برای ۱۰٬۰۰۰ مسیر نیز کار می‌کند ولی توزیع نامعلوم مقاله را حدس نمی‌زند.
function evaluate_sampled_policy(p::PlanningProblem,a::PlanningArchive,sampler::Function;
        count::Int,seed::Integer,distribution_label::AbstractString,kwargs...)
    count>0 && !isempty(strip(distribution_label)) || error(\"Explicit sampling specification required\")
    rng=MersenneTwister(seed)
    paths=(sampler(rng,i) for i in 1:count)
    result=evaluate_policy(p,a,paths;kwargs...)
    sampling=(;count,seed,distribution=String(distribution_label),paper_distribution_claim=false)
    if haskey(kwargs,:output_dir) && kwargs[:output_dir]!==nothing
        open(joinpath(kwargs[:output_dir],\"sampling.toml\"),\"w\") do io
            TOML.print(io,Dict(string(k)=>v for (k,v) in pairs(sampling)))
        end
    end
    return (;result...,sampling)
end

# تبدیل معکوس حالت دقیقاً هم‌ترتیب encode_state است؛ هیچ ظرفیت خارج شبکه گرد نمی‌شود.
function decode_state(bits,grids)
    all(x->x isa Integer && x in (0,1),bits) || error(\"Invalid state bits\")
    expected=length(A_set)*(1+sum(length(grids[k].weights) for k in (\"Cc\",\"Ce\",\"Cv\")))
    length(bits)==expected || error(\"State layout length mismatch\")
    values=Dict(k=>zeros(num_roads) for k in (\"z\",\"Cc\",\"Ce\",\"Cv\"));j=1
    for a in A_set
        values[\"z\"][a]=bits[j];j+=1
    end
    for key in (\"Cc\",\"Ce\",\"Cv\"),a in A_set
        g=grids[key];n=length(g.weights)
        values[key][a]=RC.decode(g,bits[j:j+n-1]);j+=n
    end
    # کد با ایستگاه غایب و ظرفیت مثبت، حالت فیزیکی معتبری نیست.
    for a in A_set
        values[\"z\"][a]==0 && any(values[k][a]!=0 for k in (\"Cc\",\"Ce\",\"Cv\")) &&
            error(\"Capacity at an absent station\")
    end
    return StageState(values[\"z\"],values[\"Cc\"],values[\"Ce\"],values[\"Cv\"])
end

# این مسیر قطعی از پیش‌بینی‌های موجود می‌آید؛ سناریوی تصادفی یا بدترین سناریو ادعا نمی‌شود.
function nominal_scenario(t)
    t in T_set || error(\"Invalid stage\")
    return Dict{String,Any}(\"name\"=>\"supplied forecast, nominal\",
        \"theta_t\"=>theta_fc[t],\"zeta_t\"=>zeta_fc[t],
        \"xi_wt\"=>repeat(wt_profile',num_wt,1),
        \"zeta_pv\"=>repeat(pv_profile',num_pv_pdn,1),
        \"zeta_station_pv\"=>repeat(pv_profile',num_roads,1))
end
continuous_scope(capacity_mode,initial_station_state)=bytes2hex(sha256(repr((MODEL_SOURCE_HASH,
    capacity_mode,Tuple(Int.(initial_station_state)),g7_scope_fields()))))
struct ContinuousLowerBound
    lower::Float64
    horizon::Int
    scope::String
    status::String
    integer_relaxation::Bool
end

# یک مسیر مجاز و اطلاع کامل از آینده، ریلکسیشن مسئلهٔ مقاوم غیرپیش‌نگر است.
# آزادکردن قیود صحیح نیز فقط کران پایین را ضعیف‌تر می‌کند؛ state_bits! اینجا فراخوانی نمی‌شود.
function continuous_path_lower_bound(;path=[nominal_scenario(t) for t in T_set],
        initial_state_name::String,initial_station_state::AbstractVector{<:Real},
        capacity_mode=CHARGING_CAPACITY_MODE,seconds=600.,relax_integers=true)
    g7cfg().sizing==:continuous || error(\"Continuous lower bound requires continuous physical sizing\")
    1<=length(path)<=num_periods || error(\"Invalid relaxation horizon\")
    m=create_highs_model(;silent=true,time_lim=Float64(seconds),gap=0.)
    initial_state_name in INITIAL_STATE_SCENARIOS || error(\"Unrecognized initial-state branch\")
    length(initial_station_state)==num_roads || error(\"Initial station-state length mismatch\")
    all(x -> x in (0,1), initial_station_state) || error(\"Initial station state must be binary\")
    Int.(initial_station_state)==initial_station_vector(initial_state_name) ||
        error(\"Initial station vector does not match its declared branch\")
    z0=Float64.(initial_station_state)
    prev=(;z=z0,Cc=z0.*Cc_0,Ce=z0.*Ce_0,Cv=z0.*Cv_0)
    costs=Any[]
    for t in eachindex(path)
        validate_scenario(t,path[t])
        _,v=build_stage_subproblem(t,prev.z,prev.Cc,prev.Ce,prev.Cv,path[t];
            shared_model=m,time_limit_sec=Float64(seconds),capacity_mode,initial_station_state)
        fix(v[\"alpha_cost_to_go\"],0.;force=true)
        push!(costs,objective_function(m))
        prev=(;z=v[\"z\"],Cc=v[\"Cc\"],Ce=v[\"Ce\"],Cv=v[\"Cv\"])
    end
    @objective(m,Min,sum(costs))
    relax_integers && relax_integrality(m)
    RC.solve_tracked!(m;context=\"continuous path relaxation T=\$(length(path))\")
    b=RC.min_bounds(m)
    # عدم امکان حتی یک مسیر در مدل آزادشده با کران متناهی گزارش نمی‌شود.
    lower=b.status==MOI.INFEASIBLE ? Inf : b.lower
    return ContinuousLowerBound(lower,length(path),continuous_scope(capacity_mode,initial_station_state),
        string(b.status),relax_integers)
end

# اگر کران پایین پیوسته و سیاست مقاوم شبکه‌ای هر دو موجود باشند:
# L_cont <= V_cont <= V_grid <= U_policy؛ پس U_policy-L_cont کران خطای کل است.
# این عدد خطای خالص گسسته‌سازی را جدا نمی‌کند؛ بدون UB متناهی ادعای خطای متناهی نداریم.
function capacity_error_bound(grids,a::PlanningArchive,lower::ContinuousLowerBound;
        initial_state_name::String,initial_station_state::AbstractVector{<:Real},
        capacity_mode=CHARGING_CAPACITY_MODE)
    lower.horizon==num_periods || error(\"A root-only bound cannot certify horizon discretization error\")
    lower.scope==continuous_scope(capacity_mode,initial_station_state) || error(\"Continuous/grid/initial-state assumptions differ\")
    p=physical_problem(grids;initial_state_name,initial_station_state,capacity_mode);key=RC.binary_key(p.encode(p.initial))
    sample=get(a.upper[1],key,nothing)
    sample===nothing && return (;lower=lower.lower,upper=Inf,total_error_bound=Inf,finite=false)
    sample.scope==p.scope(1) || error(\"Grid policy target mismatch\")
    isfinite(lower.lower) && lower.lower>sample.value+1e-6*max(1.,abs(sample.value)) && error(\"Bounds cross\")
    finite=isfinite(lower.lower)&&isfinite(sample.value)
    return (;lower=lower.lower,upper=sample.value,
        total_error_bound=finite ? max(0.,sample.value-lower.lower) : Inf,finite)
end

# مطالعهٔ ریشه برای سنجش زمان و حساسیت شبکه؛ نتیجهٔ آن UB سه‌دوره‌ای نیست.
function root_grid_study(specifications;initial_state_name,initial_station_state,capacity_mode,seconds=60.,output_dir=nothing)
    lower=continuous_path_lower_bound(;path=[nominal_scenario(1)],initial_state_name,initial_station_state,capacity_mode,seconds)
    rows=NamedTuple[]
    for (id,spec) in enumerate(specifications)
        g=state_grids(;spec...);p=physical_problem(g;initial_state_name,initial_station_state,capacity_mode)
        d=planning_decision(p,PlanningArchive(p.horizon),1,p.initial,nominal_scenario(1);seconds)
        push!(rows,(;study=id,charging_kw=g[\"Cc\"].step,storage_kwh=g[\"Ce\"].step,pv_kw=g[\"Cv\"].step,
            state_bits=length(p.encode(p.initial)),continuous_lp_lower=lower.lower,
            root_grid_lower=d.bounds.lower,root_grid_incumbent=d.bounds.upper,
            combined_root_error_bound=isfinite(lower.lower)&&isfinite(d.bounds.upper) ?
                max(0.,d.bounds.upper-lower.lower) : Inf,
            feasible=d.feasible,status=string(d.bounds.status),seconds=d.seconds,
            full_horizon_upper_claim=false))
    end
    if output_dir!==nothing
        mkpath(output_dir);write_rows(joinpath(output_dir,\"root_grid_sensitivity.csv\"),rows)
    end
    return (;rows,continuous_lower=lower)
end

# ممیزی دو شاخهٔ وضعیت اولیه را بدون حل مدل یا ادعای بهینگی اجرا می‌کند.
function initial_state_audit(;output_dir=@__DIR__)
    expected_roads=[2,3,10,14,16]
    existing=initial_station_vector(\"existing_five\")
    paper=initial_station_vector(\"paper_zero\")
    all(iszero,paper) || error(\"paper_zero initial state is not all-zero\")
    findall(x -> x==1,existing)==expected_roads || error(\"existing_five sites differ from supplemental Table 1\")
    length(existing)==num_roads && all(x -> x in (0,1),existing) || error(\"Invalid existing_five vector\")
    # Pure state identity audit; no unpublished physics/cost assumptions are imputed.
    paper_scope=bytes2hex(sha256(repr((\"paper_zero\",Tuple(paper),MODEL_SOURCE_HASH))))
    existing_scope=bytes2hex(sha256(repr((\"existing_five\",Tuple(existing),MODEL_SOURCE_HASH))))
    paper_scope!=existing_scope || error(\"Initial-state certificate scopes are not isolated\")
    rows=NamedTuple[]
    for name in INITIAL_STATE_SCENARIOS
        z0=initial_station_vector(name)
        role=name==\"existing_five\" ? \"paper_case_study_baseline\" : \"literal_eq37_text_sensitivity\"
        push!(rows,(scenario=name,role,initial_roads=join(findall(x -> x==1,z0),\",\"),
            station_count=sum(z0),initial_fcs_kw=sum(z0)*Cc_0,
            initial_bess_model_kwh_interpretation=sum(z0)*Ce_0,initial_onsite_pv_kw=sum(z0)*Cv_0,
            initial_z0=join(z0,\",\")))
    end
    out=joinpath(output_dir,\"REVCS19_GATE7_INITIAL_STATE_AUDIT.tsv\")
    mkpath(output_dir)
    open(out,\"w\") do io
        println(io,\"scenario\\trole\\tinitial_roads\\tstation_count\\tinitial_fcs_kw\\tinitial_bess_model_kwh_interpretation\\tinitial_onsite_pv_kw\\tinitial_z0\")
        for r in rows
            println(io,join((r.scenario,r.role,r.initial_roads,r.station_count,r.initial_fcs_kw,
                r.initial_bess_model_kwh_interpretation,r.initial_onsite_pv_kw,r.initial_z0),\"\\t\"))
        end
    end
    println(\"[PASS] PAPER_ZERO_INITIAL_STATE | roads=none | Cc=0 kW | Ce=0 kWh | Cv=0 kW\")
    println(\"[PASS] EXISTING_FIVE_INITIAL_STATE | roads=2,3,10,14,16 | Cc=\$(sum(existing)*Cc_0) kW | Ce=\$(sum(existing)*Ce_0) model-kWh interpretation (source unit unresolved) | Cv=\$(sum(existing)*Cv_0) kW\")
    println(\"[PASS] INITIAL_STATE_BRANCHES_DISTINCT | separate state vectors and certificate scopes\")
    println(\"[REVCS19 GATE7] INITIAL_STATE_AUDIT_REPORT=\$(out)\")
    return rows
end

# رابط اجرا دقت شبکه را اجباری می‌گیرد و آن را به‌عنوان دادهٔ مقاله معرفی نمی‌کند.
function g7_equivalence_report(dir::AbstractString)
    c=g7cfg()
    mkpath(dir)
    path=joinpath(dir,\"REVCS19_G7_VS_G64_EQUIVALENCE.tsv\")
    g64source=joinpath(@__DIR__,\"REVCS19_GATE6_4_CAUSAL_G64FIX.jl\")
    sourcehash=isfile(g64source) ? bytes2hex(sha256(read(g64source))) : \"NOT_PROVIDED\"
    refstatus=sourcehash==\"6939672cc0d2bd05d1772fe46488c03549f5564235bec4c33752cd4ec4bad88e\" ? \"SOURCE_SHA256_MATCH\" : \"UNVERIFIED_SOURCE_VERSION\"
    rows=[
        (\"topology_vector_sha256\",c.topology.vector_hash,\"G64 selected topology (must compare from G64 logs)\",\"REQUIRES_G64_RUN_HASH\"),
        (\"closed/open\",string(c.topology.closed)*\"/\"*string(c.topology.open),\"32/5 benchmark\",\"TOPOLOGY_SHAPE_ONLY\"),
        (\"voltage_base_kv\",string(c.voltage_base_kv),\"12.66 selected benchmark\",isapprox(c.voltage_base_kv,12.66) ? \"NUMERIC_MATCH_RECONSTRUCTED\" : \"DIFFERENT\"),
        (\"delta_p\",string(c.delta_p),\"1.0 selected benchmark\",isapprox(c.delta_p,1.0) ? \"NUMERIC_MATCH_USER_SCENARIO\" : \"DIFFERENT\"),
        (\"sigma\",string(c.sigma),\"not in G6.4 economic diagnostic\",\"NOT_COMPARABLE\"),
        (\"ope_scale\",string(c.ope_scale),\"not in G6.4 economic diagnostic\",\"NOT_COMPARABLE\"),
        (\"soc_boundary\",string(c.soc_boundary),\"cyclic/free day E0 in G6.4\",c.soc_boundary==:cyclic_free_e0 ? \"POLICY_STRUCTURE_MATCH\" : \"DIFFERENT\"),
        (\"soc_bounds\",string(c.soc_min)*\"..\"*string(c.soc_max),\"0..1 G6.4 user-selected\",c.soc_min==0 && c.soc_max==1 ? \"NUMERIC_MATCH_RECONSTRUCTED\" : \"DIFFERENT\"),
        (\"bess_power_policy\",string(c.bess_power_policy),\"fixed_20kw or scaled_half_Ce\", \"CONFIGURATION_REQUIRES_RUN_COMPARISON\"),
        (\"period3_traffic\",repr([1+theta_fc[3]-theta_err[3],1+theta_fc[3]+theta_err[3]]),\"[1.70,2.00]\",\"SOURCE_MATCH\"),
        (\"period3_DRE\",repr([1+zeta_fc[3]-zeta_err[3],1+zeta_fc[3]+zeta_err[3]]),\"[1.80,2.00]\",\"SOURCE_MATCH\"),
        (\"initial_state\",c.initial_state,\"existing_five (G6.4)\",c.initial_state==\"existing_five\" ? \"STRUCTURAL_MATCH\" : \"INTENTIONAL_BRANCH_DIFFERENCE\"),
        (\"UTN_paths\",bytes2hex(sha256(repr((Lambda_rskb,X_rska)))),\"G6.4 path arrays require independent cross-check\",\"UNVERIFIED\"),
        (\"G64_reference_source_sha256\",sourcehash,\"6939672cc0d2bd05d1772fe46488c03549f5564235bec4c33752cd4ec4bad88e\",refstatus)
    ]
    open(path,\"w\") do io
        println(io,\"parameter\\tGate7\\tGate6_4_reference_or_limit\\tstatus\")
        for row in rows
            println(io,join(row,'\\t'))
        end
    end
    println(\"[G7] Equivalence table written: \"*path)
    println(\"[G7] This is NOT a numerical or mathematical equivalence certificate.\")
    return path
end

function main(args=ARGS)
    parsed=try
        parse_gate7_cli(args)
    catch e
        open(joinpath(@__DIR__,\"REVCS19_G7_INPUT_ERROR.log\"),\"w\") do io
            println(io,\"GATE7_CLI_ERROR\\nARGS=\",repr(args),\"\\nERROR=\",sprint(showerror,e))
        end
        rethrow()
    end
    mode,opts,cfg=parsed.mode,parsed.opts,parsed.cfg
    empty!(G7_STAGE_AUDIT_ROWS)
    empty!(SOLVE_AUDIT)
    empty!(REVCSCertifiedCore.SOLVER_TRACE)
    G7_VERBOSE[]=get(opts,\"verbose\",\"false\")==\"true\"
    if mode==\"check\"
        return certified_configuration_report()
    elseif mode==\"initial-state-audit\"
        return initial_state_audit(output_dir=get(opts,\"output\",@__DIR__))
    end
    G7_ACTIVE[]=cfg
    out=get(opts,\"output\",\"revcs19_gate7_2_results\")
    mode==\"equivalence-report\" && return g7_equivalence_report(out)
    # All parsing, validation and topology checks have completed before mkdir/write.
    initial_state_name=cfg.initial_state
    initial_station_state=initial_station_vector(initial_state_name)
    grids=state_grids(charging_kw=parse(Float64,opts[\"charging-step\"]),
        storage_kwh=parse(Float64,opts[\"storage-step\"]),pv_kw=parse(Float64,opts[\"pv-step\"]))
    # Avoid requesting SCIP or solving before validating the graph, scenario, and grids.
    p=physical_problem(grids;initial_state_name,initial_station_state,capacity_mode=cfg.capacity_mode)
    forward_accept=get(opts,\"forward-accept\",\"optimal\")
    require_optimal=forward_accept==\"optimal\"
    g7_load_scip_for_plan!()
    mkpath(out)
    metadata=merge(g7_scope_metadata(),Dict{String,Any}(
        \"version\"=>\"19-gate7.2.1-runtimefix-experimental\", \"source_hash\"=>MODEL_SOURCE_HASH,
        \"arguments\"=>opts,\"initial_station_roads\"=>findall(==(1),initial_station_state),
        \"initial_fcs_capacity_kw\"=>sum(initial_station_state)*Cc_0,
        \"initial_bess_energy_model_kwh_interpretation\"=>sum(initial_station_state)*Ce_0,
        \"bess_initial_unit_note\"=>\"Supplement Table 7 prints kW; kWh interpretation unresolved\",
        \"initial_onsite_pv_capacity_kw\"=>sum(initial_station_state)*Cv_0,
        \"charging_step_kw\"=>grids[\"Cc\"].step,
        \"storage_step_kwh\"=>grids[\"Ce\"].step,
        \"pv_step_kw\"=>grids[\"Cv\"].step,
        \"road_interpretation\"=>\"undirected reference schematic / 3 shortest paths (requires independent G6.4 cross-check)\",
        \"load_allocation\"=>\"uniform per supplement Table 8\",
        \"capacity_interpretation\"=>string(cfg.capacity_mode)))
    open(joinpath(out,\"run_config.toml\"),\"w\") do io
        TOML.print(io,metadata)
    end
    g7_equivalence_report(out)
    # Import SCIP only for plan, then run all C&CG/SCIP calls in the latest world.
    # No import is performed for check, initial-state-audit, equivalence-report,
    # root-grid or continuous lower-bound paths.
    result=Base.invokelatest(g7_plan_solver_entry,p,opts,out,require_optimal)
    return result
end

function g7_plan_solver_entry(p,opts,out,require_optimal)
    return run_improved_rddp(p;iterations=parse(Int,get(opts,\"iterations\",\"1\")),
        ccg_iters=parse(Int,get(opts,\"ccg-iterations\",\"100\")),
        cut_iters=parse(Int,get(opts,\"cut-iterations\",\"60\")),
        seconds=parse(Float64,get(opts,\"seconds\",\"600\")),
        rtol=parse(Float64,get(opts,\"gap\",\"0.001\")),
        max_feasibility_repairs=parse(Int,get(opts,\"feasibility-repairs\",\"0\")),
        repair_mode=Symbol(get(opts,\"repair-mode\",\"nogood\")),
        require_optimal,output_dir=out)
end
if abspath(PROGRAM_FILE)==abspath(@__FILE__)
    main()
end
""")
    resource20("driver.jl","3501c82ff273d95f1704f3d2fba8a812c46acb933237478c1169abe7d35a5d4c","""# REVCS19 Gate 7.4.2 FIX9 -- exact sign-aware Farkas normalization audit (non-certifying).
# Frozen 96h physical model source is included without modifications.
using SHA
using JuMP
using HiGHS
import MathOptInterface as MOI

const G742_ROOT = @__DIR__
const G742_SOURCE = joinpath(G742_ROOT,\"REVCS19_GATE7_3_4_BOUNDSFIX.jl\")
const G742_TOPOLOGY = joinpath(G742_ROOT,\"REVCS19_IEEE33_BENCHMARK_TOPOLOGY.tsv\")
const G742_REAL_SOURCE_HASH = \"70f976f717ab3674ea7142717f62dc6b6c125bc3da4ec04f321c968efd1eb8f5\"
bytes2hex(sha256(read(G742_SOURCE))) == G742_REAL_SOURCE_HASH || error(\"FROZEN_PHYSICAL_SOURCE_HASH_MISMATCH\")
include(G742_SOURCE)
const G742_FARKAS_AUDIT_HOOKS = joinpath(G742_ROOT,\"REVCS19_G7_4_2_FARKAS_AUDIT_HOOKS.jl\")
isfile(G742_FARKAS_AUDIT_HOOKS) || error(\"Missing FIX7 Farkas audit hooks\")
include(G742_FARKAS_AUDIT_HOOKS)
include(joinpath(G742_ROOT,\"REVCS19_G7_4_2_FIX14_CERTIFICATE.jl\"))
include(joinpath(G742_ROOT,\"REVCS19_G7_4_2_FIX15_HANDOFF.jl\"))
include(joinpath(G742_ROOT,\"REVCS19_G7_4_2_FIX16_NATIVE_BRANCH.jl\"))
include(joinpath(G742_ROOT,\"REVCS19_G7_4_2_FIX18_SIGN_AWARE_PRODUCTION.jl\"))
include(joinpath(G742_ROOT,\"REVCS19_G7_4_2_FIX19_SAME_COLUMN_SEED.jl\"))
include(joinpath(G742_ROOT,\"REVCS19_G7_4_2_FIX17_PRODUCTION_FARKAS.jl\"))

function g742_args(args)
    options=Dict{String,String}()
    allowed=Set([\"branch\",\"mode\",\"seconds-per-solve\",\"max-iters\",\"threads\",\"relative-gap\",\"tolerance\",\"output\",\"witness-pattern\"])
    for a in args
        startswith(a,\"--\") && occursin(\"=\",a) || error(\"Expected --key=value; got \$a\")
        k,v=split(a[3:end],\"=\";limit=2)
        k in allowed && !haskey(options,k) || error(\"Unknown or repeated argument: \$k\")
        options[k]=v
    end
    branch=get(options,\"branch\",\"paper_zero\")
    mode=get(options,\"mode\",\"domain\")
    branch in (\"paper_zero\",\"existing_five\") || error(\"Unknown branch\")
    mode in (\"domain\",\"solver-check\",\"first-iter-diag\",\"farkas-structural-audit\",\"farkas-sign-aware-audit\",\"farkas-root-lp-audit\",\"farkas-mip-start-audit\",\"farkas-positive-witness-audit\",\"farkas-primal-infeasibility-audit\",\"farkas-certificate-cut-audit\",\"witness-handoff-audit\",\"native-witness-branch-audit\",\"native-production-farkas-audit\",\"full-phi3\") || error(\"Unknown mode\")
    seconds=parse(Float64,get(options,\"seconds-per-solve\",\"300\"))
    iters=parse(Int,get(options,\"max-iters\",\"3\"))
    threads=parse(Int,get(options,\"threads\",\"8\"))
    gap=parse(Float64,get(options,\"relative-gap\",\"0.001\"))
    tol=parse(Float64,get(options,\"tolerance\",\"0.00001\"))
    isfinite(seconds) && seconds>0 || error(\"Invalid seconds\")
    1<=iters<=100 && 1<=threads<=256 || error(\"Invalid iteration/thread budget\")
    isfinite(gap) && 0<=gap<1 || error(\"Invalid relative gap\")
    isfinite(tol) && 0<tol<=0.001 || error(\"Invalid tolerance\")
    witness_pattern=get(options,\"witness-pattern\",\"all-plus\")
    witness_pattern in (\"all-plus\",\"all-minus\",\"nominal\") || error(\"Invalid FIX12 witness pattern\")
    output=abspath(get(options,\"output\",joinpath(G742_ROOT,\"G7_4_2_OUTPUT\")))
    return (;branch,mode,seconds,iters,threads,gap,tol,output,witness_pattern)
end

function g742_config(o)
    cap=o.branch==\"existing_five\" ? \"printed_eq33\" : \"installed_capacity\"
    argv=[\"--mode=plan\",\"--initial-state=\$(o.branch)\",\"--capacity=\$cap\",
        \"--charging-step=100\",\"--storage-step=20\",\"--pv-step=30\",
        \"--sigma=0.05\",\"--delta-p=1.0\",\"--ope-scale=1.0\",
        \"--line-status-file=\$G742_TOPOLOGY\",\"--voltage-base-kv=12.66\",
        \"--bess-power-policy=scaled_half_Ce\",\"--soc-boundary=cyclic_free_e0\",
        \"--sizing=continuous\",\"--threads=\$(o.threads)\",
        \"--seconds=\$(o.seconds)\",\"--gap=0.0\",\"--verbose=false\"]
    return parse_gate7_cli(argv).cfg
end

# FIX15.1 parser is shared by archived evidence checks and source references.
include(joinpath(G742_ROOT,\"REVCS19_G7_4_2_FIX15_1_CSV_PARSER.jl\"))

function g742_state(o,grids)
    path=joinpath(G742_ROOT,\"reference\",o.branch,\"joint_two_witness_STAGE2_END_STATE.csv\")
    lines=readlines(path)
    header=replace.(split(strip(first(lines)),\",\"),'\"'=>\"\")
    names=(\"road\",\"z\",\"Cc_kW\",\"Ce_kWh\",\"Cv_kW\")
    all(k->k in header,names) || error(\"Missing Stage2 state columns\")
    ix=Dict(k=>findfirst(==(k),header) for k in names)
    vectors=Dict(k=>zeros(Float64,num_roads) for k in (\"z\",\"Cc\",\"Ce\",\"Cv\"))
    seen=Set{Int}()
    for line in lines[2:end]
        isempty(strip(line)) && continue
        x=replace.(split(strip(line),\",\"),'\"'=>\"\")
        a=parse(Int,x[ix[\"road\"]])
        (a in A_set && !(a in seen)) || error(\"Invalid or duplicate road \$a\")
        push!(seen,a)
        for (k,col) in ((\"z\",\"z\"),(\"Cc\",\"Cc_kW\"),(\"Ce\",\"Ce_kWh\"),(\"Cv\",\"Cv_kW\"))
            vectors[k][a]=parse(Float64,x[ix[col]])
        end
    end
    length(seen)==num_roads || error(\"Incomplete Stage2 state\")
    st=StageState(vectors[\"z\"],vectors[\"Cc\"],vectors[\"Ce\"],vectors[\"Cv\"])
    encode_state(st,grids)
    z0=Float64.(initial_station_vector(o.branch))
    all(st.z .>= z0 .- 1e-8) || error(\"Predecessor violates initial-state monotonicity\")
    hash=bytes2hex(sha256(read(path)))
    for scenario in (\"nominal\",\"stress\")
        row=g742_csvone(joinpath(G742_ROOT,\"reference\",o.branch,\"\$(scenario)_SUMMARY.csv\"))
        row[\"branch\"]==o.branch && row[\"scenario\"]==scenario || error(\"Reference branch mismatch\")
        row[\"status\"]==\"OPTIMAL_AUDITED\" && row[\"termination\"]==\"OPTIMAL\" && row[\"audit_ok\"]==\"true\" ||
            error(\"Reference scenario not independently certified\")
        row[\"source_sha256\"]==G742_REAL_SOURCE_HASH && row[\"stage2_predecessor_sha256\"]==hash ||
            error(\"Predecessor/source hash drift in Gate 7.4.1.3 evidence\")
    end
    return st,z0,hash
end

function g742_count_active(t)
    wind=count(h->wt_profile[h]*xi_wt_err_ratio>0,Tau_set)*num_wt
    solar=count(h->pv_profile[h]*zeta_pv_err_ratio>0,Tau_set)
    return (theta=Int(theta_err[t]>0),renewable=Int(zeta_err[t]>0),wind=wind,
        pdn_pv=solar*num_pv_pdn,station_pv=solar*num_roads,solar_hours=solar)
end

function g742_domain(o,grids,st,z0,state_sha)
    phi3=nothing;phi3scope=\"\"
    # This checks BOTH Phi2 and Phi3 representations. Only Phi3 is solved.
    for t in (2,3)
        counts=g742_count_active(t)
        active=counts.theta+counts.renewable+counts.wind+counts.pdn_pv+counts.station_pv
        domain=full_uncertainty_domain(t)
        domain.cardinality==big(3)^active || error(\"Full Phi\$t cardinality inconsistent\")
        model=Model()
        symbolic_bits,_,_=symbolic_uncertainty(model,t)
        length(symbolic_bits)==2active || error(\"Symbolic full-Phi\$t bit dimension mismatch\")
        seed=first(domain.factory())
        validate_scenario(t,seed)
        scope=physical_cost_scope(t,grids;domain,capacity_mode=g7cfg().capacity_mode,initial_station_state=z0)
        rows=[(;branch=o.branch,stage=t,active_coordinates=active,binary_indicators=length(symbolic_bits),
            theta_coordinates=counts.theta,renewable_growth_coordinates=counts.renewable,
            wind_coordinates=counts.wind,pdn_pv_coordinates=counts.pdn_pv,
            station_pv_coordinates=counts.station_pv,solar_active_hours=counts.solar_hours,
            exact_domain_cardinality=string(domain.cardinality),scope,domain_scope=domain.scope,
            predecessor_sha256=state_sha,physical_source_sha256=MODEL_SOURCE_HASH,
            full_domain_constructed=true,full_domain_oracle_solved=false)]
        write_rows(joinpath(o.output,\"PHI\$(t)_DOMAIN_PREFLIGHT.csv\"),rows)
        println(\"G742_DOMAIN stage=\$t branch=\$(o.branch) active=\$active binary_indicators=\$(length(symbolic_bits)) scenarios=3^\$active scope=\$scope\")
        if t==3
            phi3=domain;phi3scope=scope
        end
    end
    return phi3,phi3scope
end

function g742_solver_check()
    # SCIP is preloaded before entering g742_main in the latest Julia world.
    optimizer=g7_scip_optimizer()
    m=Model(optimizer)
    set_silent(m)
    @variable(m,x,Bin)
    @objective(m,Max,x)
    Base.invokelatest(optimize!,m)
    termination_status(m)==MOI.OPTIMAL && has_values(m) && abs(value(x)-1.0)<=1e-7 ||
        error(\"SCIP_SMOKE_TEST_NOT_OPTIMAL\")
    println(\"G742_SCIP_SMOKE_TEST=PASS\")
end

function g742_write_scenario(out,scenario)
    scenario isa AbstractDict || return false
    validate_scenario(3,scenario)
    write_rows(joinpath(out,\"ADVERSARIAL_GROWTH.csv\"),[(;
        theta_t=scenario[\"theta_t\"],zeta_t=scenario[\"zeta_t\"],
        omega_u_plus=scenario[\"omega_u_plus\"],omega_u_minus=scenario[\"omega_u_minus\"],
        omega_p_plus=scenario[\"omega_p_plus\"],omega_p_minus=scenario[\"omega_p_minus\"])])
    for (label,key) in ((\"WT\",\"xi_wt\"),(\"PV_PDN\",\"zeta_pv\"),(\"PV_STATION\",\"zeta_station_pv\"))
        mat=scenario[key]
        write_rows(joinpath(out,\"ADVERSARIAL_\$(label).csv\"),
            [(;unit=r,hour=h,physical_profile=mat[r,h]) for r in axes(mat,1) for h in Tau_set])
    end
    return true
end

function g742_audit_witness(o,st,z0,grids,scenario)
    validate_scenario(3,scenario)
    m,v=build_certified_stage(3,st,scenario,grids;
        direction=:lower,lower_cuts=REVCSCertifiedCore.BinaryCut[],seconds=o.seconds,
        capacity_mode=g7cfg().capacity_mode,initial_station_state=z0)
    fix(v[\"alpha_cost_to_go\"],0.0;force=true)
    set_optimizer_attribute(m,\"mip_rel_gap\",0.0)
    set_optimizer_attribute(m,\"time_limit\",o.seconds)
    optimize!(m)
    term=termination_status(m)
    if term==MOI.INFEASIBLE
        return (;status=\"INFEASIBLE_REPRODUCED\",termination=string(term),
            lower=Inf,upper=Inf,independent_residual=NaN,model_violation=NaN)
    end
    b=REVCSCertifiedCore.min_bounds(m)
    if !b.feasible
        return (;status=\"NO_AUDITED_INCUMBENT\",termination=string(term),
            lower=b.lower,upper=b.upper,independent_residual=NaN,model_violation=NaN)
    end
    violations=primal_feasibility_report(m;atol=o.tol)
    empty!(G7_STAGE_AUDIT_ROWS)
    audit=audit_stage_solution!(m,v,3;tol=o.tol)
    write_rows(joinpath(o.output,\"WITNESS_INDEPENDENT_EQUATIONS.csv\"),G7_STAGE_AUDIT_ROWS)
    maxviolation=isempty(violations) ? 0.0 : maximum(Float64.(collect(values(violations))))
    write_rows(joinpath(o.output,\"WITNESS_JUMP_VIOLATIONS.csv\"),
        [(;constraint=string(k),violation=Float64(val)) for (k,val) in violations])
    st3=solved_state(v,grids)
    gridvalid=maximum(abs.(Float64.(encode_state(st3,grids)).-value.(v[\"state_bits\"]));init=0.0)<=o.tol
    objresidual=abs(objective_value(m)-value(discounted_stage_physical_cost(3,v)))
    ok=term==MOI.OPTIMAL && isempty(violations) &&
        audit.status==\"PASS_INDEPENDENT_SUBSET\" && gridvalid &&
        objresidual<=o.tol*max(1.0,abs(objective_value(m)))
    return (;status=ok ? \"OPTIMAL_AUDITED\" : \"UNRESOLVED_OR_AUDIT_FAILED\",
        termination=string(term),lower=b.lower,upper=b.upper,
        independent_residual=Float64(audit.worst),model_violation=maxviolation)
end

# FIX6: This is a separate, NONCERTIFYING diagnostic of the first native C&CG
# iteration. It uses the original frozen model-building/solving functions and
# adds only phase checkpoints; it does not change the physical source or model.
function g742_diag_event(o, phase; detail=\"\")
    line=\"G742_DIAG phase=\$(phase) \$(detail)\"
    println(line)
    flush(stdout)
    open(joinpath(o.output,\"FIRST_ITER_DIAG_EVENTS.tsv\"),\"a\") do io
        println(io,string(time()),\"\\t\",phase,\"\\t\",detail)
        flush(io)
    end
    return nothing
end

function g742_first_iter_diag(o,cfg,grids,st,z0,domain)
    g742_diag_event(o,\"START\";detail=\"scope=first_native_CCG_iteration_noncertifying\")
    seed=first(domain.factory())
    g742_diag_event(o,\"INNER_BUILD_START\")
    inner,_=build_certified_stage(3,st,seed,grids;
        direction=:lower,seconds=o.seconds,capacity_mode=cfg.capacity_mode,
        initial_station_state=z0)
    REVCSCertifiedCore.ensure_solver_column!(inner)
    g742_diag_event(o,\"INNER_BUILD_DONE\";
        detail=\"vars=\$(num_variables(inner)) cons=\$(num_constraints(inner;count_variable_in_set_constraints=true))\")
    set_time_limit_sec(inner,Float64(o.seconds))
    g742_diag_event(o,\"INNER_SOLVE_START\")
    REVCSCertifiedCore.solve_tracked!(inner;context=\"g742_diag_inner\")
    row=REVCSCertifiedCore.min_bounds(inner)
    g742_diag_event(o,\"INNER_SOLVE_DONE\";
        detail=\"status=\$(row.status) feasible=\$(row.feasible) lower=\$(row.lower) upper=\$(row.upper)\")
    if row.status==MOI.INFEASIBLE || !row.feasible
        g742_diag_event(o,\"COMPLETE\";detail=\"inner_result_not_feasible;_no_Oracle_claim\")
        return nothing
    end
    g742_diag_event(o,\"INTEGER_PATTERN_START\")
    pattern=REVCSCertifiedCore.integer_pattern(inner)
    g742_diag_event(o,\"INTEGER_PATTERN_DONE\")
    symbolic_factory=m->symbolic_uncertainty(m,3)
    block=(m,u)->build_certified_stage(3,st,u,grids;
        direction=:lower,seconds=o.seconds,capacity_mode=cfg.capacity_mode,
        initial_station_state=z0,shared_model=m)
    columns=[pattern]
    g742_diag_event(o,\"FARKAS_BUILD_START\")
    fm,_=REVCSCertifiedCore.symbolic_master(columns,symbolic_factory,block,HiGHS.Optimizer;
        ray=true,seconds=o.seconds)
    g742_diag_event(o,\"FARKAS_BUILD_DONE\";
        detail=\"vars=\$(num_variables(fm)) cons=\$(num_constraints(fm;count_variable_in_set_constraints=true))\")
    for (_,set_type) in list_of_constraint_types(fm)
        set_type <: MOI.Indicator && error(\"Diagnostic Farkas master has unexpected indicators\")
    end
    g742_diag_event(o,\"FARKAS_SOLVE_START\")
    REVCSCertifiedCore.solve_tracked!(fm;context=\"g742_diag_farkas\")
    fstatus=termination_status(fm)
    ffeasible=has_values(fm) && primal_status(fm)==MOI.FEASIBLE_POINT
    fbound=try objective_bound(fm) catch; Inf end
    fvalue=ffeasible ? objective_value(fm) : NaN
    gate=REVCSCertifiedCore.farkas_gate(fstatus,ffeasible,fvalue,fbound;tol=1e-8)
    g742_diag_event(o,\"FARKAS_SOLVE_DONE\";
        detail=\"status=\$fstatus feasible=\$ffeasible bound=\$fbound objective=\$fvalue gate=\$gate\")
    if gate != :covered
        g742_diag_event(o,\"COMPLETE\";detail=\"farkas_gate=\$gate;_no_Oracle_claim\")
        return nothing
    end
    g742_diag_event(o,\"OPTIMALITY_BUILD_START\")
    master,_=REVCSCertifiedCore.symbolic_master(columns,symbolic_factory,block,g7_scip_optimizer();
        seconds=o.seconds)
    g742_diag_event(o,\"OPTIMALITY_BUILD_DONE\";
        detail=\"vars=\$(num_variables(master)) cons=\$(num_constraints(master;count_variable_in_set_constraints=true))\")
    g742_diag_event(o,\"OPTIMALITY_SOLVE_START\")
    REVCSCertifiedCore.solve_tracked!(master;context=\"g742_diag_optimality\")
    st_master=termination_status(master)
    ub=try objective_bound(master) catch; Inf end
    g742_diag_event(o,\"OPTIMALITY_SOLVE_DONE\";detail=\"status=\$st_master bound=\$ub\")
    g742_diag_event(o,\"COMPLETE\";detail=\"first_iteration_components_examined;_no_Oracle_claim\")
    return nothing
end

function g742_farkas_event(o,phase;detail=\"\")
    line=\"G742_FARKAS_AUDIT phase=\$(phase) \$(detail)\"
    println(line);flush(stdout)
    open(joinpath(o.output,\"FARKAS_AUDIT_EVENTS.tsv\"),\"a\") do io
        println(io,string(time()),\"\\t\",phase,\"\\t\",detail);flush(io)
    end
    return nothing
end

function g742_highs_smoke_check()
    m=Model(HiGHS.Optimizer);set_silent(m)
    @variable(m,x,Bin);@objective(m,Max,x)
    optimize!(m)
    termination_status(m)==MOI.OPTIMAL && has_values(m) && abs(value(x)-1.0)<=1e-7 ||
        error(\"HIGHS_SMOKE_TEST_NOT_OPTIMAL\")
    println(\"G742_HIGHS_SMOKE_TEST=PASS\");flush(stdout)
end

# FIX13: create an independent numerical Phi3 realization using the frozen
# create_uncertainty_scenario implementation; cross-check each physical
# parameter against the separate symbolic_uncertainty model evaluated at the
# identical complete 3-state bit assignment (no full-domain enumeration).
function g742_fix13_realization(kind::String)
    kind in (\"all-plus\",\"all-minus\",\"nominal\") || error(\"FIX13_BAD_PATTERN\")
    plus=Float64(kind==\"all-plus\")
    minus=Float64(kind==\"all-minus\")
    wp=zeros(num_wt,num_tau);wm=similar(wp);fill!(wm,0.0)
    pp=zeros(num_pv_pdn,num_tau);pm=similar(pp);fill!(pm,0.0)
    sp=zeros(num_roads,num_tau);sm=similar(sp);fill!(sm,0.0)
    active=0
    for w in WT_set,h in Tau_set
        if wt_profile[h]*xi_wt_err_ratio>0
            wp[w,h]=plus;wm[w,h]=minus;active+=1
        end
    end
    for p in PV_PDN_set,h in Tau_set
        if pv_profile[h]*zeta_pv_err_ratio>0
            pp[p,h]=plus;pm[p,h]=minus;active+=1
        end
    end
    for a in 1:num_roads,h in Tau_set
        if pv_profile[h]*zeta_pv_err_ratio>0
            sp[a,h]=plus;sm[a,h]=minus;active+=1
        end
    end
    oup=theta_err[3]>0 ? plus : 0.0
    oum=theta_err[3]>0 ? minus : 0.0
    opp=zeta_err[3]>0 ? plus : 0.0
    opm=zeta_err[3]>0 ? minus : 0.0
    active+=Int(theta_err[3]>0)+Int(zeta_err[3]>0)
    scenario=create_uncertainty_scenario(\"FIX13 independent numerical \$kind\",3,
        oup,oum,opp,opm,wp,wm,pp,pm,sp,sm)
    validate_scenario(3,scenario)
    aux=Model()
    bits,symbolic,_=symbolic_uncertainty(aux,3)
    length(bits)==2active || error(\"FIX13_ACTIVE_COORDINATE_MISMATCH\")
    assignments=Dict{VariableRef,Float64}()
    for i in 1:active
        assignments[bits[2i-1]]=plus
        assignments[bits[2i]]=minus
    end
    function as_number(expr)
        expr isa Number && return Float64(expr)
        return Float64(JuMP.value(v->assignments[v],expr))
    end
    maxerr=maximum((abs(as_number(symbolic[k])-Float64(scenario[k]))
        for k in (\"theta_t\",\"zeta_t\"));init=0.0)
    for k in (\"xi_wt\",\"zeta_pv\",\"zeta_station_pv\")
        sym=symbolic[k];num=scenario[k]
        size(sym)==size(num) || error(\"FIX13_PROFILE_DIMENSIONS_DIFFER\")
        for ix in eachindex(num)
            maxerr=max(maxerr,abs(as_number(sym[ix])-Float64(num[ix])))
        end
    end
    isfinite(maxerr) && maxerr<=1e-8 || error(\"FIX13_SYMBOLIC_NUMERIC_SCENARIO_MISMATCH\")
    return scenario,(;pattern=kind,active_coordinates=active,
        plus_coordinates=Int(plus)*active,minus_coordinates=Int(minus)*active,
        symbolic_numerical_max_difference=maxerr,scenario_validated=true,
        physical_source_hash=G742_REAL_SOURCE_HASH)
end

# FIX13: independently rebuild the PHYSICAL recourse LP at exactly the
# numerical realization and integer pattern used by the Farkas diagnostic.
# In particular, no relaxation of unfixed 0/1 recourse decisions is allowed.
function g742_fix13_primal_replay(o,cfg,grids,st,z0,pattern;return_model::Bool=false)
    sc,scenario_audit=g742_fix13_realization(o.witness_pattern)
    write_rows(joinpath(o.output,\"FIX13_SCENARIO_IDENTITY.csv\"),[scenario_audit])
    g742_farkas_event(o,\"PRIMAL_BUILD_START\";
        detail=\"same_inner_pattern=\$(length(pattern.values)) full_domain_pattern=\$(o.witness_pattern)\")
    m,_=build_certified_stage(3,st,sc,grids;
        direction=:lower,lower_cuts=REVCSCertifiedCore.BinaryCut[],
        seconds=o.seconds,capacity_mode=cfg.capacity_mode,
        initial_station_state=z0)
    before_vars=num_variables(m)
    before_cons=num_constraints(m;count_variable_in_set_constraints=true)
    iv=filter(v->is_binary(v)||is_integer(v),all_variables(m))
    layout=[index(v).value for v in iv]
    binary_count=count(is_binary,iv)
    layout==pattern.indices || error(\"FIX13_PRIMAL_INTEGER_LAYOUT_DIFFERENT\")
    length(iv)==length(pattern.values) || error(\"FIX13_PRIMAL_INTEGER_COUNT_MISMATCH\")
    g742_farkas_event(o,\"PRIMAL_BUILD_DONE\";
        detail=\"vars=\$before_vars cons=\$before_cons integers=\$(length(iv))\")
    REVCSCertifiedCore.fix_pattern!(m,pattern)
    leftover=count(v->is_binary(v)||is_integer(v),all_variables(m))
    leftover==0 || error(\"FIX13_PRIMAL_IS_NOT_AN_LP\")
    all(is_fixed(v) && abs(fix_value(v)-k)<=1e-8
        for (v,k) in zip(iv,pattern.values)) ||
        error(\"FIX13_PATTERN_NOT_EXACTLY_FIXED\")
    set_time_limit_sec(m,Float64(o.seconds))
    g742_farkas_event(o,\"PRIMAL_SOLVE_START\";
        detail=\"solver=HiGHS seconds=\$(o.seconds) threads=\$(o.threads) pattern_fixed=true\")
    elapsed=@elapsed optimize!(m)
    term=termination_status(m);ps=primal_status(m);ds=dual_status(m)
    feasible=has_values(m) && ps==MOI.FEASIBLE_POINT
    primal_obj=feasible ? Float64(objective_value(m)) : NaN
    output=(;pattern=o.witness_pattern,termination_status=string(term),
        primal_status=string(ps),dual_status=string(ds),
        independent_primal_infeasible=(term==MOI.INFEASIBLE && !feasible),
        independent_primal_feasible=feasible,primal_objective=primal_obj,
        solve_seconds=elapsed,seconds_per_solve=o.seconds,
        variables_before_fix=before_vars,constraints_before_fix=before_cons,
        original_integer_variables=length(iv),integer_layout_exact_match=true,
        original_integer_values_fixed_exactly=true,remaining_discrete_variables=leftover,
        fixed_pattern_source=\"same_execution_inner_pattern\",
        solver=\"HiGHS.Optimizer\",primal_model_source=\"frozen_build_certified_stage\",
        numerical_phi3_source=\"create_uncertainty_scenario\",
        symbolic_numerical_max_difference=scenario_audit.symbolic_numerical_max_difference,
        full_phi3_certified=false)
    write_rows(joinpath(o.output,\"FIX13_PRIMAL_LP_STATUS.csv\"),[output])
    g742_farkas_event(o,\"PRIMAL_SOLVE_DONE\";
        detail=\"termination=\$(term) primal=\$(ps) dual=\$(ds) feasible=\$feasible\")
    return return_model ? (;output,model=m,all_binary=(binary_count==length(iv))) : output
end

function g742_farkas_structural_audit(o,cfg,grids,st,z0,domain;sign_aware::Bool=false,root_lp_diag::Bool=false,mip_start_diag::Bool=false,positive_diag::Bool=false,primal_diag::Bool=false,certificate_diag::Bool=false)
    empty!(REVCSCertifiedCore.SOLVER_TRACE)
    g742_farkas_event(o,\"START\";detail=sign_aware ?
        \"noncertifying_exact_sign_aware_normalization_audit\" :
        \"noncertifying_first_iteration_structural_audit\")
    if sign_aware
        g742_farkas_event(o,\"SIGN_NORM_EQUIVALENCE_START\")
        tests=REVCSCertifiedCore.farkas_audit_sign_normalization_selftest(;threads=o.threads)
        length(tests)==12 && all(x->x.passed,tests) || error(\"FIX9_SELFTEST_INCOMPLETE\")
        write_rows(joinpath(o.output,\"FARKAS_NORMALIZATION_EQUIVALENCE.csv\"),tests)
        g742_farkas_event(o,\"SIGN_NORM_EQUIVALENCE_DONE\";detail=\"cases=\$(length(tests)) result=PASS\")
    end
    seed=first(domain.factory())
    g742_farkas_event(o,\"INNER_BUILD_START\")
    inner,_=build_certified_stage(3,st,seed,grids;
        direction=:lower,seconds=o.seconds,capacity_mode=cfg.capacity_mode,
        initial_station_state=z0)
    REVCSCertifiedCore.ensure_solver_column!(inner)
    g742_farkas_event(o,\"INNER_BUILD_DONE\";
        detail=\"vars=\$(num_variables(inner)) cons=\$(num_constraints(inner;count_variable_in_set_constraints=true))\")
    set_time_limit_sec(inner,Float64(o.seconds))
    g742_farkas_event(o,\"INNER_SOLVE_START\";detail=\"solver=HiGHS threads=\$(o.threads) mip_rel_gap=0.0\")
    REVCSCertifiedCore.solve_tracked!(inner;context=\"g742_fix7_inner\")
    row=REVCSCertifiedCore.min_bounds(inner)
    g742_farkas_event(o,\"INNER_SOLVE_DONE\";
        detail=\"status=\$(row.status) feasible=\$(row.feasible) lower=\$(row.lower) upper=\$(row.upper)\")
    if !row.feasible
        write_rows(joinpath(o.output,\"FARKAS_STRUCTURAL_SUMMARY.csv\"),[(;
            branch=o.branch,status=\"INNER_NO_INCUMBENT\",inner_status=string(row.status),
            inner_feasible=false,inner_lower=row.lower,inner_upper=row.upper,
            integer_pattern_entries=0,model_variables=0,model_constraints=0,
            expected_model_variables=0,variable_count_delta=0,
            expected_model_constraints=0,constraint_count_delta=0,
            constraint_type_count_delta=0,build_seconds=NaN,build_allocated_bytes=0,
            farkas_status=\"NOT_BUILT\",farkas_feasible=false,farkas_bound=Inf,farkas_objective=NaN,
            farkas_gate=\"NOT_REACHED\")])
        g742_farkas_event(o,\"COMPLETE\";detail=\"inner_no_incumbent;_no_Oracle_claim\")
        return false
    end
    g742_farkas_event(o,\"INTEGER_PATTERN_START\")
    pattern=REVCSCertifiedCore.integer_pattern(inner)
    g742_farkas_event(o,\"INTEGER_PATTERN_DONE\";detail=\"integer_pattern_entries=\$(length(pattern.values))\")
    symbolic_factory=m->symbolic_uncertainty(m,3)
    block=(m,u)->build_certified_stage(3,st,u,grids;
        direction=:lower,seconds=o.seconds,capacity_mode=cfg.capacity_mode,
        initial_station_state=z0,shared_model=m)
    g742_farkas_event(o,\"FARKAS_BUILD_START\";detail=\"columns=1 optimizer=HiGHS.Optimizer\")
    build_measurement=@timed REVCSCertifiedCore.farkas_audit_symbolic_master(
        [pattern],symbolic_factory,block,HiGHS.Optimizer;
        seconds=o.seconds,threads=o.threads,sign_aware=sign_aware)
    audited=build_measurement.value
    fm=audited.model;metrics=audited.metrics
    g742_farkas_event(o,\"FARKAS_BUILD_DONE\";
        detail=\"vars=\$(metrics[\"model_variables\"]) cons=\$(metrics[\"model_constraints\"]) build_seconds=\$(build_measurement.time) build_gc_seconds=\$(build_measurement.gctime) build_cumulative_allocated_bytes=\$(build_measurement.bytes) variable_delta=\$(metrics[\"variable_count_delta\"]) constraint_delta=\$(metrics[\"constraint_count_delta\"]) type_delta=\$(metrics[\"constraint_type_count_delta\"])\" )

    if sign_aware
        # Compare with the exact historical FIX8 audit of paper_zero, not assumed data.
        baseline_file=joinpath(G742_ROOT,\"FIX8_BASELINE_FARKAS_STRUCTURAL_AUDIT.csv\")
        legacy=Dict{String,Int}()
        for (i,line) in enumerate(eachline(baseline_file))
            i==1 && continue
            fields=split(replace(strip(line),'\"'=>\"\"),\",\")
            length(fields)==2 || error(\"FIX9_BASELINE_CSV_MALFORMED\")
            legacy[fields[1]]=parse(Int,fields[2])
        end
        signed=get(metrics,\"sign_aware_eliminated_abs_variables\",0)
        nvars=metrics[\"model_variables\"]
        ncons=metrics[\"model_constraints\"]
        expected_legacy_vars=nvars+signed
        expected_legacy_cons=ncons+4signed
        known_branch=o.branch==\"paper_zero\"
        if known_branch
            expected_legacy_vars==legacy[\"model_variables\"] || error(\"FIX9_BASELINE_VARIABLE_MISMATCH\")
            expected_legacy_cons==legacy[\"model_constraints\"] || error(\"FIX9_BASELINE_CONSTRAINT_MISMATCH\")
            signed==legacy[\"less_equal_sides\"]+legacy[\"greater_equal_sides\"] ||
                error(\"FIX9_BASELINE_SIGNED_DUAL_MISMATCH\")
            metrics[\"absolute_value_variables\"]==legacy[\"equality_sides\"] ||
                error(\"FIX9_BASELINE_FREE_DUAL_MISMATCH\")
        end
        metrics[\"variable_count_delta\"]==0 && metrics[\"constraint_count_delta\"]==0 ||
            error(\"FIX9_INTERNAL_COUNT_DELTA_NONZERO\")
        write_rows(joinpath(o.output,\"FARKAS_NORMALIZATION_REDUCTION.csv\"),[(;
            branch=o.branch,comparison_to_fix8_verified=known_branch,
            baseline_model_variables=known_branch ? legacy[\"model_variables\"] : expected_legacy_vars,
            baseline_model_constraints=known_branch ? legacy[\"model_constraints\"] : expected_legacy_cons,
            sign_aware_model_variables=nvars,sign_aware_model_constraints=ncons,
            eliminated_abs_variables=signed,eliminated_abs_variable_bounds=2signed,
            eliminated_abs_linear_rows=2signed,
            free_dual_abs_variables_retained=metrics[\"absolute_value_variables\"],
            signed_dual_nonpositive=metrics[\"sign_aware_nonpositive_duals\"],
            signed_dual_nonnegative=metrics[\"sign_aware_nonnegative_duals\"],
            exact_projection_preserves_normalization=true,
            math_equivalence_selftest_cases=12,
            model_variable_count_delta=metrics[\"variable_count_delta\"],
            model_constraint_count_delta=metrics[\"constraint_count_delta\"],
            oracle_certified=false)])
        g742_farkas_event(o,\"SIGN_NORM_REDUCTION_VERIFIED\";
            detail=\"old_vars=\$expected_legacy_vars new_vars=\$nvars old_cons=\$expected_legacy_cons new_cons=\$ncons eliminated_abs=\$signed\")
    end
    metric_rows=[(;metric=k,count=v) for (k,v) in sort(collect(metrics);by=x->x.first)]
    write_rows(joinpath(o.output,\"FARKAS_STRUCTURAL_AUDIT.csv\"),metric_rows)
    constraint_rows=[(;function_type=k[1],set_type=k[2],count=v)
        for (k,v) in sort(collect(audited.constraint_types);by=x->x.first)]
    write_rows(joinpath(o.output,\"FARKAS_CONSTRAINT_TYPES.csv\"),constraint_rows)
    primal_rows=[(;set_type=k,count=v) for (k,v) in sort(collect(audited.primal_set_types);by=x->x.first)]
    write_rows(joinpath(o.output,\"FARKAS_PRIMAL_CONSTRAINT_TYPES.csv\"),primal_rows)

    write_rows(joinpath(o.output,\"FARKAS_SOLVER_CONFIG.csv\"),[
        (;parameter=\"optimizer\",value=\"HiGHS.Optimizer\",explicit_in_audit_model=\"YES\",note=\"diagnostic Farkas optimizer\"),
        (;parameter=\"time_limit_seconds\",value=o.seconds,explicit_in_audit_model=\"YES\",note=\"same SecondsPerSolve CLI value\"),
        (;parameter=\"threads\",value=o.threads,explicit_in_audit_model=\"YES\",note=\"same Threads CLI value passed explicitly to diagnostic Farkas model\"),
        (;parameter=\"presolve\",value=\"on\",explicit_in_audit_model=\"YES\",note=\"matches existing create_highs_model setting\"),
        (;parameter=\"mip_rel_gap\",value=\"PRODUCTION_DEFAULT_NOT_OVERRIDDEN\",explicit_in_audit_model=\"NO\",note=\"RelativeGap CLI is the outer C&CG stopping tolerance, not a HiGHS MIP gap; retain production default\"),
        (;parameter=\"outer_ccg_relative_gap\",value=o.gap,explicit_in_audit_model=\"N/A\",note=\"recorded only; structural audit does not run C&CG convergence\"),
        (;parameter=\"output_flag\",value=\"SILENT_DURING_BUILD\",explicit_in_audit_model=\"YES\",note=\"set_silent; audit unsilences only for logging\")])

    write_rows(joinpath(o.output,\"FARKAS_BUILD_MEASUREMENT.csv\"),[
        (;build_seconds=build_measurement.time,build_gc_seconds=build_measurement.gctime,
          cumulative_allocated_bytes=build_measurement.bytes,
          interpretation=\"Julia @timed cumulative allocation; NOT peak resident memory\")])
    open(joinpath(o.output,\"FARKAS_MEMORY_NOTE.txt\"),\"w\") do io
        println(io,\"build_allocated_bytes is Julia @timed cumulative allocation over model construction.\")
        println(io,\"It is NOT peak RAM, working set, or private bytes.\")
        println(io,\"Peak process memory is not measured by this diagnostic.\")
    end

    if positive_diag
        sign_aware && !root_lp_diag && !mip_start_diag ||
            error(\"FIX12_REQUIRES_SIGN_AWARE_FIXED_PATTERN_ONLY\")
        g742_farkas_event(o,\"FIXED_PATTERN_LP_START\";
            detail=\"pattern=\$(o.witness_pattern) time_limit=\$(o.seconds) threads=\$(o.threads)\")
        try
            unset_silent(fm)
        catch e
            println(\"G742_FIX12_LOG_WARNING \",sprint(showerror,e))
        end
        witnessfile=joinpath(o.output,\"FARKAS_FIXED_PATTERN_WITNESS.tsv\")
        fixed=REVCSCertifiedCore.farkas_fixed_pattern_lp!(audited;
            pattern=o.witness_pattern,seconds=Float64(o.seconds),
            witness_path=witnessfile)
        write_rows(joinpath(o.output,\"FARKAS_FIXED_PATTERN_LP.csv\"),[fixed])
        if primal_diag
            # The earlier FIX12 archive does NOT preserve the inner column.
            # Persist the exact column now and compare BOTH tests in this run.
            pfile=joinpath(o.output,\"FIX13_INNER_INTEGER_PATTERN.tsv\")
            open(pfile,\"w\") do io
                println(io,\"variable_index\\tvalue\")
                for (ix,k) in zip(pattern.indices,pattern.values)
                    println(io,ix,'\\t',k)
                end
            end
            phash=bytes2hex(sha256(read(pfile)))
            g742_farkas_event(o,\"PRIMAL_REPLAY_START\";
                detail=\"pattern_sha256=\$phash witness_positive=\$(fixed.positive_candidate)\")
            replay=g742_fix13_primal_replay(o,cfg,grids,st,z0,pattern;return_model=certificate_diag)
            primal=certificate_diag ? replay.output : replay
            # We can confirm consistency only if a new positive Farkas
            # candidate exists in THIS run on the IDENTICAL saved column.
            contradiction=fixed.positive_candidate && primal.independent_primal_feasible
            corroborated=fixed.positive_candidate && primal.independent_primal_infeasible
            interpretation=contradiction ? \"CONTRADICTION_UNCERTIFIED\" :
                (corroborated ? \"NUMERIC_PRIMAL_FARKAS_CONSISTENT\" :
                \"UNRESOLVED_PRIMAL_FARKAS_CROSSCHECK\")
            write_rows(joinpath(o.output,\"FIX13_CROSSCHECK.csv\"),[(;
                branch=o.branch,uncertainty_pattern=o.witness_pattern,
                inner_pattern_sha256=phash,inner_pattern_variables=length(pattern.values),
                same_run_same_pattern=true,
                farkas_positive_candidate=fixed.positive_candidate,
                farkas_objective=fixed.objective_value,
                farkas_numerically_validated=fixed.numerically_validated,
                primal_termination_status=primal.termination_status,
                primal_status=primal.primal_status,
                independent_primal_infeasible=primal.independent_primal_infeasible,
                independent_primal_feasible=primal.independent_primal_feasible,
                primal_farkas_consistent=corroborated,
                contradiction_detected=contradiction,
                interpretation=interpretation,full_phi3_certified=false)])
            g742_farkas_event(o,\"PRIMAL_REPLAY_DONE\";
                detail=\"gate=\$interpretation pattern_sha256=\$phash\")
            # Fail closed on contradictory evidence; do not emit a PASS.
            contradiction && error(\"FIX13_PRIMAL_DUAL_CONTRADICTION\")
            if certificate_diag
                g742_farkas_event(o,\"PRIMAL_CERTIFICATE_AUDIT_START\")
                rayfile=joinpath(o.output,\"FIX14_PRIMAL_DUAL_RAY.tsv\")
                cert=try
                    g742_fix14_ray_audit(replay.model;tolerance=1e-8,rayfile=rayfile)
                catch err
                    open(joinpath(o.output,\"FIX14_CERTIFICATE_EXTRACTION_ERROR.txt\"),\"w\") do io
                        showerror(io,err,catch_backtrace())
                    end
                    g742_fix14_unavailable_certificate(replay.model,err)
                end
                write_rows(joinpath(o.output,\"FIX14_PRIMAL_CERTIFICATE_AUDIT.csv\"),[cert])
                scope=g742_fix14_cut_scope(o,pattern,replay.all_binary,cert,
                    fixed.positive_candidate && fixed.numerically_validated &&
                    primal.independent_primal_infeasible)
                write_rows(joinpath(o.output,\"FIX14_FEASIBILITY_CUT_SCOPE.csv\"),[scope])
                g742_farkas_event(o,\"PRIMAL_CERTIFICATE_AUDIT_DONE\";
                    detail=\"status=\$(cert.status) valid=\$(cert.certificate_numerically_validated) scoped=\$(scope.scoped_infeasibility_certificate_validated) root_cut=false\")
            end
        end
        # Full-domain coverage is never inferred from testing just one pattern.
        open(joinpath(o.output,\"FARKAS_SOLVER_STATUS.txt\"),\"w\") do io
            println(io,\"TERMINATION_STATUS=\",fixed.termination_status)
            println(io,\"PRIMAL_STATUS=\",fixed.primal_status)
            println(io,\"FIXED_PATTERN=\",fixed.pattern)
            println(io,\"FIXED_PATTERN_GATE=\",fixed.interpretation)
            println(io,\"FARKAS_GATE=unresolved\")
            println(io,\"FULL_DOMAIN_FARKAS_CERTIFIED=NO\")
            println(io,\"ORACLE_CERTIFIED=NO\")
        end
        write_rows(joinpath(o.output,\"FARKAS_SOLVER_TRACE.csv\"),[(;
            context=\"g742_fix12_fixed_pattern_lp\",sense=\"MAX_SENSE\",
            termination=fixed.termination_status,primal=fixed.primal_status,
            variables=fixed.original_variables,constraints=fixed.original_constraints,
            seconds=fixed.solve_seconds,allocated_bytes=0,gc_seconds=0,
            incumbent=fixed.objective_value,bound=fixed.objective_bound)])
        write_rows(joinpath(o.output,\"FARKAS_STRUCTURAL_SUMMARY.csv\"),[(;
            branch=o.branch,status=(certificate_diag ? \"PRIMAL_CERTIFICATE_CUT_SCOPE_AUDIT_COMPLETED_NOT_CERTIFIED\" : (primal_diag ? \"PRIMAL_FARKAS_CROSSCHECK_COMPLETED_NOT_CERTIFIED\" : \"FARKAS_FIXED_PATTERN_AUDIT_COMPLETED_NOT_CERTIFIED\")),
            inner_status=string(row.status),inner_feasible=row.feasible,
            inner_lower=row.lower,inner_upper=row.upper,
            integer_pattern_entries=length(pattern.values),
            model_variables=metrics[\"model_variables\"],
            model_constraints=metrics[\"model_constraints\"],
            expected_model_variables=metrics[\"expected_model_variables\"],
            variable_count_delta=metrics[\"variable_count_delta\"],
            expected_model_constraints=metrics[\"expected_model_constraints\"],
            constraint_count_delta=metrics[\"constraint_count_delta\"],
            constraint_type_count_delta=metrics[\"constraint_type_count_delta\"],
            build_seconds=build_measurement.time,
            build_gc_seconds=build_measurement.gctime,
            build_allocated_bytes=build_measurement.bytes,
            farkas_status=\"FIXED_PATTERN_\"*fixed.termination_status,
            farkas_feasible=fixed.solver_reported_feasible,
            farkas_bound=fixed.objective_bound,
            farkas_objective=fixed.objective_value,farkas_gate=\"unresolved\")])
        g742_farkas_event(o,\"FIXED_PATTERN_LP_DONE\";
            detail=\"pattern=\$(fixed.pattern) termination=\$(fixed.termination_status) feasible=\$(fixed.solver_reported_feasible) objective=\$(fixed.objective_value) positive=\$(fixed.positive_candidate) numeric_valid=\$(fixed.numerically_validated) fixed_pattern_only=true full_oracle=NO\")
        g742_farkas_event(o,\"COMPLETE\";detail=\"fixed_pattern_diagnostic_only_no_Oracle_claim\")
        return true
    end

    if root_lp_diag
        sign_aware || error(\"FIX10_REQUIRES_SIGN_AWARE_FARKAS_MASTER\")
        g742_farkas_event(o,\"ZERO_VECTOR_CHECK_START\";detail=\"all_constraints_with_variable_domain_sets\")
        zero_result=REVCSCertifiedCore.farkas_audit_zero_assignment(fm)
        write_rows(joinpath(o.output,\"FARKAS_ZERO_VECTOR_CHECK.csv\"),[zero_result])
        g742_farkas_event(o,\"ZERO_VECTOR_CHECK_DONE\";
            detail=\"checked=\$(zero_result.checked_constraints) violated=\$(zero_result.violated_constraints) max=\$(zero_result.maximum_violation)\")
        zero_result.all_zero_feasible || error(\"FIX10_ZERO_ASSIGNMENT_NOT_FEASIBLE\")
        # Enable solver progress logging before the standalone root LP audit.
        try
            unset_silent(fm)
        catch e
            println(\"G742_ROOT_LP_LOG_WARNING \",sprint(showerror,e))
        end
        g742_farkas_event(o,\"ROOT_LP_SOLVE_START\";
            detail=\"relax_integrality=true;seconds=\$(o.seconds);threads=\$(o.threads);presolve=on\")
        lp,restored=REVCSCertifiedCore.farkas_audit_root_lp!(fm;seconds=Float64(o.seconds))
        write_rows(joinpath(o.output,\"FARKAS_ROOT_LP_STATUS.csv\"),[lp])
        write_rows(joinpath(o.output,\"FARKAS_MIP_RESTORE_CHECK.csv\"),[restored])
        g742_farkas_event(o,\"ROOT_LP_SOLVE_DONE\";
            detail=\"status=\$(lp.termination_status) primal=\$(lp.primal_status) dual=\$(lp.dual_status) feasible=\$(lp.feasible_point) objective=\$(lp.objective_value) fractional=\$(lp.lp_fractional_count) elapsed=\$(lp.solve_seconds)\")
        g742_farkas_event(o,\"MIP_RESTORE_VERIFIED\";
            detail=\"vars=\$(restored.model_variables) cons=\$(restored.model_constraints) discrete=\$(restored.restored_discrete_variables)\")
    end

    if mip_start_diag
        sign_aware && !root_lp_diag || error(\"FIX11_START_MODE_REQUIRES_SIGN_AWARE_NON_LP\")
        g742_farkas_event(o,\"MIP_START_ZERO_VERIFY_START\")
        startinfo=REVCSCertifiedCore.farkas_audit_start_zero!(fm)
        write_rows(joinpath(o.output,\"FARKAS_ZERO_VECTOR_CHECK.csv\"),[
            REVCSCertifiedCore.farkas_audit_zero_assignment(fm)])
        write_rows(joinpath(o.output,\"FARKAS_MIP_START_SUPPORT.csv\"),[startinfo])
        g742_farkas_event(o,\"MIP_START_ZERO_VERIFY_DONE\";
            detail=\"support=\$(startinfo.start_probe) submitted=\$(startinfo.start_values_submitted) readback=\$(startinfo.start_values_readback) model_unchanged=\$(startinfo.no_model_modification)\")
        g742_farkas_event(o,\"MIP_START_SOLVER_ACCEPTANCE_UNKNOWN\";
            detail=\"JuMP_start_readback_is_not_solver_acceptance\")
    end

    # Display-only override for this diagnostic so the HiGHS presolve/search log is captured.
    try
        unset_silent(fm)
    catch e
        println(\"G742_FARKAS_AUDIT_LOG_UNSILENCE_WARNING \",sprint(showerror,e))
    end
    g742_farkas_event(o,\"FARKAS_SOLVE_START\";
        detail=\"time_limit=\$(o.seconds);threads=\$(o.threads);presolve=on;mip_rel_gap=production_default_not_overridden;outer_ccg_relative_gap=\$(o.gap)_is_not_a_HiGHS_MIP_gap\")
    REVCSCertifiedCore.solve_tracked!(fm;context=\"g742_fix7_farkas\")
    fstatus=termination_status(fm)
    ffeasible=has_values(fm) && primal_status(fm)==MOI.FEASIBLE_POINT
    fbound=try objective_bound(fm) catch; Inf end
    fvalue=ffeasible ? objective_value(fm) : NaN
    gate=REVCSCertifiedCore.farkas_gate(fstatus,ffeasible,fvalue,fbound;tol=1e-8)
    if mip_start_diag
        incumbent=REVCSCertifiedCore.farkas_audit_mip_incumbent(fm)
        write_rows(joinpath(o.output,\"FARKAS_MIP_INCUMBENT_AUDIT.csv\"),[incumbent])
        g742_farkas_event(o,\"MIP_INCUMBENT_AUDIT_DONE\";
            detail=\"solver_reported=\$(incumbent.solver_reported_incumbent) independently_validated=\$(incumbent.independent_incumbent_validated) constraints=\$(incumbent.constraints_checked) violations=\$(incumbent.violated_constraints) start_acceptance=UNVERIFIED\")
    end
    write_rows(joinpath(o.output,\"FARKAS_SOLVER_TRACE.csv\"),REVCSCertifiedCore.SOLVER_TRACE)
    open(joinpath(o.output,\"FARKAS_SOLVER_STATUS.txt\"),\"w\") do io
        println(io,\"TERMINATION_STATUS=\",fstatus)
        println(io,\"PRIMAL_STATUS=\",primal_status(fm))
        println(io,\"HAS_FEASIBLE_POINT=\",ffeasible)
        println(io,\"OBJECTIVE_BOUND=\",fbound)
        println(io,\"OBJECTIVE_VALUE=\",fvalue)
        println(io,\"FARKAS_GATE=\",gate)
        println(io,\"ORACLE_CERTIFIED=NO\")
    end
    write_rows(joinpath(o.output,\"FARKAS_STRUCTURAL_SUMMARY.csv\"),[(;
        branch=o.branch,status=mip_start_diag ? \"FARKAS_MIP_START_AUDIT_COMPLETED_NOT_CERTIFIED\" :
            (root_lp_diag ? \"FARKAS_ROOT_LP_AUDIT_COMPLETED_NOT_CERTIFIED\" :
            (sign_aware ? \"FARKAS_SIGN_AWARE_AUDIT_COMPLETED_NOT_CERTIFIED\" :
                \"FARKAS_STRUCTURAL_AUDIT_COMPLETED_NOT_CERTIFIED\")),
        inner_status=string(row.status),inner_feasible=row.feasible,
        inner_lower=row.lower,inner_upper=row.upper,
        integer_pattern_entries=length(pattern.values),
        model_variables=metrics[\"model_variables\"],model_constraints=metrics[\"model_constraints\"],
        expected_model_variables=metrics[\"expected_model_variables\"],
        variable_count_delta=metrics[\"variable_count_delta\"],
        expected_model_constraints=metrics[\"expected_model_constraints\"],
        constraint_count_delta=metrics[\"constraint_count_delta\"],
        constraint_type_count_delta=metrics[\"constraint_type_count_delta\"],
        build_seconds=build_measurement.time,build_gc_seconds=build_measurement.gctime,
        build_allocated_bytes=build_measurement.bytes,
        farkas_status=string(fstatus),farkas_feasible=ffeasible,
        farkas_bound=fbound,farkas_objective=fvalue,farkas_gate=string(gate))])
    g742_farkas_event(o,\"FARKAS_SOLVE_DONE\";
        detail=\"status=\$fstatus feasible=\$ffeasible bound=\$fbound objective=\$fvalue gate=\$gate\")
    g742_farkas_event(o,\"COMPLETE\";detail=\"structural_audit_only;_no_Oracle_claim\")
    return true
end

function g742_write_status(out,vals)
    open(joinpath(out,\"GATE_STATUS.txt\"),\"w\") do f
        for (k,v) in vals
            println(f,k,\"=\",v)
        end
    end
end

function g742_main(args)
    o=g742_args(args)
    mkpath(o.output)
    cfg=g742_config(o)
    G7_ACTIVE[]=cfg
    G7_VERBOSE[]=false
    grids=state_grids(;charging_kw=100.0,storage_kwh=20.0,pv_kw=30.0)
    st,z0,state_sha=g742_state(o,grids)
    domain,scope=g742_domain(o,grids,st,z0,state_sha)
    if o.mode==\"domain\"
        g742_write_status(o.output,[
            \"GATE_7_4_2_STATUS\"=>\"DOMAIN_PREFLIGHT_PASS_NOT_SOLVED\",
            \"BRANCH\"=>o.branch,\"FULL_PHI3_DOMAIN_CHECKED\"=>\"YES\",
            \"FULL_PHI3_ORACLE_CERTIFIED\"=>\"NO\",\"FULL_PHI2_PHI3_POLICY_CERTIFIED\"=>\"NO\",
            \"ROOT_GLOBAL_UPPER_BOUND_CERTIFIED\"=>\"NO\"])
        return 0
    end
    g742_solver_check()
    if o.mode==\"solver-check\"
        g742_write_status(o.output,[\"GATE_7_4_2_STATUS\"=>\"SCIP_SMOKE_PASS_ORACLE_NOT_RUN\",
            \"FULL_PHI3_ORACLE_CERTIFIED\"=>\"NO\",\"FULL_PHI2_PHI3_POLICY_CERTIFIED\"=>\"NO\"])
        return 0
    end
    println(\"G742_NATIVE_FULL_PHI3_START branch=\$(o.branch) max_iters=\$(o.iters) per_solve_sec=\$(o.seconds) gap=\$(o.gap)\")
    flush(stdout)
    empty!(REVCSCertifiedCore.SOLVER_TRACE)
    start=time()
    r=fix20_continue(o,cfg,grids,st,z0,state_sha,scope,domain)
    elapsed=time()-start
    r.bound_role==:exact && r.scope==scope || error(\"Oracle bound role/scope mismatch\")
    write_rows(joinpath(o.output,\"NATIVE_SOLVER_TRACE.csv\"),REVCSCertifiedCore.SOLVER_TRACE)
    write_rows(joinpath(o.output,\"NATIVE_ITERATIONS.csv\"),
        [(;iteration=hasproperty(x,:iteration) ? x.iteration : 0,
           phase=hasproperty(x,:phase) ? string(x.phase) : \"\",
           lower=hasproperty(x,:lower) ? x.lower : NaN,
           upper=hasproperty(x,:upper) ? x.upper : NaN,
           columns=hasproperty(x,:columns) ? x.columns : 0,
           master_complete=hasproperty(x,:master_complete) ? x.master_complete : false,
           feasibility_status=hasproperty(x,:feasibility_status) ? x.feasibility_status : \"\",
           feasibility_bound=hasproperty(x,:feasibility_bound) ? x.feasibility_bound : NaN,
           feasibility_incumbent=hasproperty(x,:feasibility_incumbent) ? x.feasibility_incumbent : NaN)
         for x in r.history])
    stress=g742_csvone(joinpath(G742_ROOT,\"reference\",o.branch,\"stress_SUMMARY.csv\"))
    known_lb=parse(Float64,stress[\"lower_bound\"])
    isnan(known_lb) && error(\"Invalid reference stress lower bound\")
    bound_consistent=!isfinite(r.upper) || r.upper+o.tol*max(1.0,abs(r.upper),abs(known_lb))>=known_lb
    bounds_ordered=!((isfinite(r.lower) && isfinite(r.upper)) &&
        r.lower>r.upper+o.tol*max(1.0,abs(r.lower),abs(r.upper)))
    scenario_valid=false
    witness_status=\"NOT_REPLAYED\"; witness_lb=NaN;witness_ub=NaN
    if r.scenario isa AbstractDict
        scenario_valid=g742_write_scenario(o.output,r.scenario)
    end
    if (r.converged || r.infeasible) && scenario_valid
        replay=g742_audit_witness(o,st,z0,grids,r.scenario)
        witness_status=replay.status; witness_lb=replay.lower;witness_ub=replay.upper
        write_rows(joinpath(o.output,\"WITNESS_REPLAY_SUMMARY.csv\"),[replay])
    end
    r.infeasible && r.converged && error(\"Contradictory oracle statuses\")
    certified_finite=r.converged && r.reason==:gap && !r.infeasible &&
        isfinite(r.lower) && isfinite(r.upper) &&
        REVCSCertifiedCore.gap_closed(r.lower,r.upper,o.gap) &&
        bound_consistent && bounds_ordered && scenario_valid &&
        witness_status==\"OPTIMAL_AUDITED\" &&
        witness_lb>=r.lower-o.tol*max(1.0,abs(r.lower),abs(witness_lb)) &&
        witness_lb<=r.upper+o.tol*max(1.0,abs(r.upper),abs(witness_lb))
    certified_infeasible=r.infeasible && r.reason==:robust_infeasible &&
        scenario_valid && witness_status==\"INFEASIBLE_REPRODUCED\"
    status=certified_finite ? \"CERTIFIED_FULL_PHI3_WITHIN_GAP\" :
        certified_infeasible ? \"CERTIFIED_INFEASIBLE_FIXED_PREDECESSOR_FULL_PHI3\" :
        \"UNRESOLVED_FULL_PHI3_ORACLE\"
    write_rows(joinpath(o.output,\"ORACLE_SUMMARY.csv\"),[(;
        branch=o.branch,status,mode=o.mode,source_sha256=MODEL_SOURCE_HASH,
        predecessor_sha256=state_sha,cost_scope=scope,domain_cardinality=string(domain.cardinality),
        lower_bound=r.lower,upper_bound=r.upper,baseline_stress_validated_lower_bound=known_lb,
        known_stress_bound_respected=bound_consistent,oracle_bounds_ordered=bounds_ordered,
        converged=r.converged,infeasible=r.infeasible,reason=string(r.reason),
        columns=length(r.columns),iterations=length(r.history),
        witness_scenario_valid=scenario_valid,witness_replay_status=witness_status,
        witness_replay_LB=witness_lb,witness_replay_UB=witness_ub,
        elapsed_seconds=elapsed,finite_gap_target=o.gap,
        full_phi3_oracle_certified=(certified_finite || certified_infeasible),
        full_multistage_phi2_phi3_certified=false,root_global_upper_bound_certified=false)])
    g742_write_status(o.output,[\"GATE_7_4_2_STATUS\"=>status,\"BRANCH\"=>o.branch,
        \"FIXED_PREDECESSOR_SHA256\"=>state_sha,\"FULL_PHI3_ORACLE_CERTIFIED\"=>
           ((certified_finite || certified_infeasible) ? \"YES\" : \"NO\"),
        \"FULL_PHI2_PHI3_POLICY_CERTIFIED\"=>\"NO\",\"ROOT_GLOBAL_UPPER_BOUND_CERTIFIED\"=>\"NO\",
        \"ORACLE_LOWER_BOUND\"=>r.lower,\"ORACLE_UPPER_BOUND\"=>r.upper,
        \"KNOWN_STRESS_LOWER_BOUND\"=>known_lb,\"NATIVE_REASON\"=>string(r.reason)])
    println(\"G742_RESULT branch=\$(o.branch) status=\$status reason=\$(r.reason) LB=\$(r.lower) UB=\$(r.upper)\")
    flush(stdout)
    return certified_finite || certified_infeasible ? 0 : 4
end
""")
    resource20("REVCS19_IEEE33_BENCHMARK_TOPOLOGY.tsv","a9d19bf3577b73a350f5bf85f4ae00864a8f0ef40846e05520990e654a603e77","""# TEST SCENARIO ONLY: standard IEEE 33-bus normally closed branches 1..32, open ties 33..37
# NOT VERIFIED AS THE SWITCH STATUS OF THE MODIFIED XIONG ET AL. NETWORK
line_id	closed
1	1
2	1
3	1
4	1
5	1
6	1
7	1
8	1
9	1
10	1
11	1
12	1
13	1
14	1
15	1
16	1
17	1
18	1
19	1
20	1
21	1
22	1
23	1
24	1
25	1
26	1
27	1
28	1
29	1
30	1
31	1
32	1
33	0
34	0
35	0
36	0
37	0
""")
    resource20("checkpoint/FIX17_COLUMN_PATTERN.tsv","cbc93a9cad9074973a726e41e0ea754b9404f3561909dd1f3c771a5a05945be2","""variable_index	value
1	1
2	0
3	1
4	0
5	0
6	0
7	0
8	1
9	1
10	1
11	0
12	0
13	0
14	1
15	0
16	1
17	1
18	0
19	0
20	1
21	0
22	0
23	0
24	0
25	0
26	0
27	0
28	0
29	0
30	0
31	0
32	0
33	0
34	0
35	0
36	0
37	0
38	0
39	0
40	0
41	1
42	0
43	1
44	0
45	0
46	0
47	0
48	1
49	1
50	1
51	0
52	0
53	0
54	1
55	0
56	1
57	1
58	0
59	0
60	1
61	1
62	0
63	1
64	0
65	0
66	0
67	0
68	1
69	1
70	1
71	0
72	0
73	0
74	1
75	0
76	1
77	1
78	0
79	0
80	1
81	1
82	0
83	1
84	0
85	0
86	0
87	0
88	1
89	1
90	1
91	0
92	0
93	0
94	1
95	0
96	1
97	1
98	0
99	0
100	1
281	1
282	0
283	1
284	0
285	0
286	0
287	0
288	1
289	1
290	1
291	0
292	0
293	0
294	1
295	0
296	1
297	1
298	0
299	0
300	1
301	1
302	0
303	1
304	0
305	0
306	0
307	0
308	1
309	1
310	1
311	0
312	0
313	0
314	1
315	0
316	1
317	1
318	0
319	0
320	1
321	1
322	0
323	1
324	0
325	0
326	0
327	0
328	1
329	1
330	1
331	0
332	0
333	0
334	1
335	0
336	1
337	1
338	0
339	0
340	1
341	1
342	0
343	0
344	0
345	0
346	0
347	0
348	1
349	0
350	1
351	0
352	0
353	0
354	0
355	0
356	1
357	1
358	0
359	0
360	1
361	0
362	0
363	1
364	0
365	0
366	0
367	0
368	0
369	0
370	0
371	0
372	0
373	0
374	0
375	0
376	1
377	0
378	0
379	0
380	0
381	1
382	0
383	1
384	0
385	0
386	0
387	0
388	0
389	1
390	0
391	0
392	0
393	0
394	1
395	0
396	1
397	0
398	0
399	0
400	1
401	1
402	0
403	1
404	0
405	0
406	0
407	0
408	1
409	1
410	1
411	0
412	0
413	0
414	1
415	0
416	1
417	1
418	0
419	0
420	1
421	1
422	0
423	1
424	0
425	0
426	0
427	0
428	1
429	1
430	1
431	0
432	0
433	0
434	1
435	0
436	1
437	1
438	0
439	0
440	1
441	1
442	0
443	1
444	0
445	0
446	0
447	0
448	1
449	1
450	1
451	0
452	0
453	0
454	1
455	0
456	0
457	1
458	0
459	0
460	1
461	1
462	0
463	1
464	0
465	0
466	0
467	0
468	1
469	1
470	1
471	0
472	0
473	0
474	1
475	0
476	1
477	1
478	0
479	0
480	1
481	1
482	0
483	1
484	0
485	0
486	0
487	0
488	1
489	1
490	1
491	0
492	0
493	0
494	1
495	0
496	1
497	1
498	0
499	0
500	1
501	1
502	0
503	0
504	0
505	0
506	0
507	0
508	0
509	1
510	0
511	0
512	0
513	0
514	0
515	0
516	0
517	0
518	0
519	0
520	0
521	1
522	0
523	0
524	0
525	0
526	0
527	0
528	0
529	1
530	0
531	0
532	0
533	0
534	0
535	0
536	0
537	0
538	0
539	0
540	0
541	1
542	0
543	0
544	0
545	0
546	0
547	0
548	0
549	1
550	1
551	0
552	0
553	0
554	0
555	0
556	1
557	0
558	0
559	0
560	0
561	0
562	0
563	1
564	0
565	0
566	0
567	0
568	1
569	1
570	1
571	0
572	0
573	0
574	1
575	0
576	1
577	1
578	0
579	0
580	1
581	1
582	0
583	1
584	0
585	0
586	0
587	0
588	1
589	1
590	1
591	0
592	0
593	0
594	1
595	0
596	1
597	1
598	0
599	0
600	1
601	1
602	0
603	1
604	0
605	0
606	0
607	0
608	1
609	1
610	1
611	0
612	0
613	0
614	1
615	0
616	1
617	1
618	0
619	0
620	1
621	1
622	0
623	1
624	0
625	0
626	0
627	0
628	1
629	1
630	1
631	0
632	0
633	0
634	1
635	0
636	1
637	1
638	0
639	0
640	1
641	1
642	0
643	1
644	0
645	0
646	0
647	0
648	1
649	1
650	1
651	0
652	0
653	0
654	1
655	0
656	1
657	1
658	0
659	0
660	1
661	1
662	0
663	1
664	0
665	0
666	0
667	0
668	1
669	1
670	1
671	0
672	0
673	0
674	1
675	0
676	1
677	1
678	0
679	0
680	1
681	1
682	0
683	1
684	0
685	0
686	0
687	0
688	1
689	1
690	1
691	0
692	0
693	0
694	1
695	0
696	1
697	1
698	0
699	0
700	1
701	1
702	0
703	1
704	0
705	0
706	0
707	0
708	1
709	1
710	1
711	0
712	0
713	0
714	1
715	0
716	1
717	1
718	0
719	0
720	1
721	1
722	0
723	1
724	0
725	0
726	0
727	0
728	1
729	1
730	1
731	0
732	0
733	0
734	1
735	0
736	1
737	1
738	0
739	0
740	1
741	1
742	0
743	1
744	0
745	0
746	0
747	0
748	1
749	1
750	1
751	0
752	0
753	0
754	1
755	0
756	1
757	1
758	0
759	0
760	1
761	1
762	0
763	1
764	0
765	0
766	0
767	0
768	1
769	1
770	1
771	0
772	0
773	0
774	1
775	0
776	1
777	1
778	0
779	0
780	1
781	1
782	0
783	1
784	0
785	0
786	0
787	0
788	1
789	1
790	1
791	0
792	0
793	0
794	0
795	0
796	1
797	0
798	0
799	0
800	1
801	1
802	0
803	1
804	0
805	0
806	0
807	0
808	1
809	1
810	1
811	0
812	0
813	0
814	1
815	0
816	1
817	1
818	0
819	0
820	1
821	1
822	0
823	1
824	0
825	0
826	0
827	0
828	1
829	1
830	1
831	0
832	0
833	0
834	1
835	0
836	1
837	1
838	0
839	0
840	1
841	0
842	0
843	0
844	0
845	0
846	0
847	0
848	0
849	0
850	0
851	0
852	0
853	0
854	0
855	0
856	0
857	0
858	0
859	0
860	0
861	1
862	0
863	1
864	0
865	0
866	0
867	0
868	1
869	0
870	1
871	0
872	0
873	0
874	1
875	0
876	1
877	1
878	0
879	0
880	1
881	1
882	0
883	1
884	0
885	0
886	0
887	0
888	1
889	1
890	1
891	0
892	0
893	0
894	1
895	0
896	1
897	1
898	0
899	0
900	1
901	1
902	0
903	1
904	0
905	0
906	0
907	0
908	1
909	1
910	1
911	0
912	0
913	0
914	1
915	0
916	1
917	1
918	0
919	0
920	1
921	1
922	0
923	1
924	0
925	0
926	0
927	0
928	1
929	1
930	1
931	0
932	0
933	0
934	1
935	0
936	1
937	1
938	0
939	0
940	1
941	1
942	0
943	1
944	0
945	0
946	0
947	0
948	1
949	1
950	1
951	0
952	0
953	0
954	1
955	0
956	1
957	1
958	0
959	0
960	1
961	1
962	0
963	1
964	0
965	0
966	0
967	0
968	1
969	1
970	1
971	0
972	0
973	0
974	1
975	0
976	1
977	1
978	0
979	0
980	1
981	0
982	0
983	0
984	0
985	0
986	0
987	0
988	0
989	0
990	0
991	0
992	0
993	0
994	0
995	0
996	0
997	0
998	0
999	0
1000	0
1001	1
1002	0
1003	1
1004	0
1005	0
1006	0
1007	0
1008	1
1009	1
1010	1
1011	0
1012	0
1013	0
1014	1
1015	0
1016	1
1017	1
1018	0
1019	0
1020	1
1021	0
1022	0
1023	0
1024	0
1025	0
1026	0
1027	0
1028	0
1029	0
1030	0
1031	0
1032	0
1033	0
1034	0
1035	0
1036	0
1037	0
1038	0
1039	0
1040	0
1041	1
1042	0
1043	1
1044	0
1045	0
1046	0
1047	0
1048	1
1049	1
1050	1
1051	0
1052	0
1053	0
1054	1
1055	0
1056	1
1057	1
1058	0
1059	0
1060	1
1061	1
1062	0
1063	1
1064	0
1065	0
1066	0
1067	0
1068	1
1069	1
1070	1
1071	0
1072	0
1073	0
1074	1
1075	0
1076	1
1077	1
1078	0
1079	0
1080	1
1081	1
1082	0
1083	1
1084	0
1085	0
1086	0
1087	0
1088	1
1089	1
1090	1
1091	0
1092	0
1093	0
1094	1
1095	0
1096	1
1097	1
1098	0
1099	0
1100	1
1101	1
1102	0
1103	1
1104	0
1105	0
1106	0
1107	0
1108	0
1109	1
1110	1
1111	0
1112	0
1113	0
1114	1
1115	0
1116	1
1117	1
1118	0
1119	0
1120	1
1121	1
1122	0
1123	1
1124	0
1125	0
1126	0
1127	0
1128	1
1129	1
1130	0
1131	0
1132	0
1133	0
1134	1
1135	0
1136	1
1137	1
1138	0
1139	0
1140	1
1141	1
1142	0
1143	1
1144	0
1145	0
1146	0
1147	0
1148	1
1149	1
1150	1
1151	0
1152	0
1153	0
1154	1
1155	0
1156	1
1157	1
1158	0
1159	0
1160	1
1161	0
1162	0
1163	0
1164	0
1165	0
1166	0
1167	0
1168	0
1169	0
1170	0
1171	0
1172	0
1173	0
1174	0
1175	0
1176	0
1177	0
1178	0
1179	0
1180	0
1181	1
1182	0
1183	1
1184	0
1185	0
1186	0
1187	0
1188	1
1189	1
1190	1
1191	0
1192	0
1193	0
1194	1
1195	0
1196	1
1197	1
1198	0
1199	0
1200	1
1201	1
1202	0
1203	1
1204	0
1205	0
1206	0
1207	0
1208	1
1209	1
1210	1
1211	0
1212	0
1213	0
1214	1
1215	0
1216	1
1217	1
1218	0
1219	0
1220	1
1221	1
1222	0
1223	1
1224	0
1225	0
1226	0
1227	0
1228	1
1229	0
1230	1
1231	0
1232	0
1233	0
1234	1
1235	0
1236	1
1237	1
1238	0
1239	0
1240	1
1241	1
1242	0
1243	1
1244	0
1245	0
1246	0
1247	0
1248	1
1249	1
1250	1
1251	0
1252	0
1253	0
1254	1
1255	0
1256	1
1257	1
1258	0
1259	0
1260	1
1261	1
1262	0
1263	1
1264	0
1265	0
1266	0
1267	0
1268	1
1269	1
1270	1
1271	0
1272	0
1273	0
1274	1
1275	0
1276	1
1277	1
1278	0
1279	0
1280	1
1281	1
1282	0
1283	1
1284	0
1285	0
1286	0
1287	0
1288	1
1289	1
1290	1
1291	0
1292	0
1293	0
1294	1
1295	0
1296	1
1297	1
1298	0
1299	0
1300	1
1301	1
1302	0
1303	1
1304	0
1305	0
1306	0
1307	0
1308	1
1309	1
1310	1
1311	0
1312	0
1313	0
1314	1
1315	0
1316	1
1317	1
1318	0
1319	0
1320	1
1321	0
1322	0
1323	0
1324	0
1325	0
1326	0
1327	0
1328	0
1329	0
1330	0
1331	0
1332	0
1333	0
1334	0
1335	0
1336	0
1337	0
1338	0
1339	0
1340	0
1341	0
1342	0
1343	0
1344	0
1345	0
1346	0
1347	0
1348	0
1349	0
1350	0
1351	0
1352	0
1353	0
1354	0
1355	0
1356	0
1357	0
1358	0
1359	0
1360	0
1361	1
1362	0
1363	1
1364	0
1365	0
1366	0
1367	0
1368	1
1369	1
1370	1
1371	0
1372	0
1373	0
1374	1
1375	0
1376	1
1377	1
1378	0
1379	0
1380	1
1381	1
1382	0
1383	1
1384	0
1385	0
1386	0
1387	0
1388	1
1389	1
1390	1
1391	0
1392	0
1393	0
1394	1
1395	0
1396	1
1397	1
1398	0
1399	0
1400	1
1401	1
1402	0
1403	1
1404	0
1405	0
1406	0
1407	0
1408	1
1409	1
1410	1
1411	0
1412	0
1413	0
1414	1
1415	0
1416	1
1417	1
1418	0
1419	0
1420	1
1421	1
1422	0
1423	1
1424	0
1425	0
1426	0
1427	0
1428	1
1429	1
1430	1
1431	0
1432	0
1433	0
1434	1
1435	0
1436	1
1437	1
1438	0
1439	0
1440	1
1441	1
1442	0
1443	1
1444	0
1445	0
1446	0
1447	0
1448	1
1449	1
1450	1
1451	0
1452	0
1453	0
1454	1
1455	0
1456	1
1457	1
1458	0
1459	0
1460	1
1461	0
1462	0
1463	0
1464	0
1465	0
1466	0
1467	0
1468	0
1469	1
1470	0
1471	0
1472	0
1473	0
1474	0
1475	0
1476	0
1477	0
1478	0
1479	0
1480	0
1481	0
1482	0
1483	0
1484	0
1485	0
1486	0
1487	0
1488	0
1489	0
1490	0
1491	0
1492	0
1493	0
1494	0
1495	0
1496	0
1497	0
1498	0
1499	0
1500	0
1501	1
1502	0
1503	0
1504	0
1505	0
1506	0
1507	0
1508	0
1509	0
1510	0
1511	0
1512	0
1513	0
1514	0
1515	0
1516	0
1517	0
1518	0
1519	0
1520	0
1521	1
1522	0
1523	0
1524	0
1525	0
1526	0
1527	0
1528	0
1529	1
1530	1
1531	0
1532	0
1533	0
1534	1
1535	0
1536	1
1537	0
1538	0
1539	0
1540	0
1541	1
1542	0
1543	1
1544	0
1545	0
1546	0
1547	0
1548	1
1549	1
1550	1
1551	0
1552	0
1553	0
1554	1
1555	0
1556	1
1557	1
1558	0
1559	0
1560	1
1561	1
1562	0
1563	1
1564	0
1565	0
1566	0
1567	0
1568	1
1569	1
1570	1
1571	0
1572	0
1573	0
1574	1
1575	0
1576	1
1577	1
1578	0
1579	0
1580	1
1581	1
1582	0
1583	1
1584	0
1585	0
1586	0
1587	0
1588	1
1589	1
1590	1
1591	0
1592	0
1593	0
1594	1
1595	0
1596	1
1597	1
1598	0
1599	0
1600	1
1601	0
1602	0
1603	0
1604	0
1605	0
1606	0
1607	0
1608	0
1609	0
1610	0
1611	0
1612	0
1613	0
1614	0
1615	0
1616	1
1617	0
1618	0
1619	0
1620	1
1621	1
1622	0
1623	1
1624	0
1625	0
1626	0
1627	0
1628	1
1629	0
1630	1
1631	0
1632	0
1633	0
1634	1
1635	0
1636	0
1637	0
1638	0
1639	0
1640	0
1641	0
1642	0
1643	0
1644	0
1645	0
1646	0
1647	0
1648	0
1649	1
1650	0
1651	0
1652	0
1653	0
1654	0
1655	0
1656	0
1657	1
1658	0
1659	0
1660	0
1661	1
1662	0
1663	1
1664	0
1665	0
1666	0
1667	0
1668	1
1669	1
1670	1
1671	0
1672	0
1673	0
1674	1
1675	0
1676	1
1677	1
1678	0
1679	0
1680	1
1681	1
1682	0
1683	1
1684	0
1685	0
1686	0
1687	0
1688	1
1689	1
1690	1
1691	0
1692	0
1693	0
1694	1
1695	0
1696	1
1697	1
1698	0
1699	0
1700	1
1701	1
1702	0
1703	1
1704	0
1705	0
1706	0
1707	0
1708	1
1709	1
1710	1
1711	0
1712	0
1713	0
1714	1
1715	0
1716	1
1717	1
1718	0
1719	0
1720	1
1721	1
1722	0
1723	1
1724	0
1725	0
1726	0
1727	0
1728	1
1729	1
1730	1
1731	0
1732	0
1733	0
1734	1
1735	0
1736	1
1737	1
1738	0
1739	0
1740	1
1741	1
1742	0
1743	1
1744	0
1745	0
1746	0
1747	0
1748	1
1749	1
1750	1
1751	0
1752	0
1753	0
1754	1
1755	0
1756	1
1757	1
1758	0
1759	0
1760	1
1761	1
1762	0
1763	1
1764	0
1765	0
1766	0
1767	0
1768	1
1769	1
1770	1
1771	0
1772	0
1773	0
1774	1
1775	0
1776	1
1777	1
1778	0
1779	0
1780	1
1781	0
1782	0
1783	0
1784	0
1785	0
1786	0
1787	0
1788	0
1789	0
1790	0
1791	0
1792	0
1793	0
1794	0
1795	0
1796	0
1797	0
1798	0
1799	0
1800	0
1801	0
1802	0
1803	1
1804	0
1805	0
1806	0
1807	0
1808	0
1809	0
1810	0
1811	0
1812	0
1813	0
1814	0
1815	0
1816	0
1817	0
1818	0
1819	0
1820	0
1821	1
1822	0
1823	1
1824	0
1825	0
1826	0
1827	0
1828	1
1829	1
1830	1
1831	0
1832	0
1833	0
1834	1
1835	0
1836	1
1837	1
1838	0
1839	0
1840	1
1841	1
1842	0
1843	1
1844	0
1845	0
1846	0
1847	0
1848	1
1849	1
1850	1
1851	0
1852	0
1853	0
1854	1
1855	0
1856	1
1857	1
1858	0
1859	0
1860	1
1861	0
1862	0
1863	0
1864	0
1865	0
1866	0
1867	0
1868	0
1869	1
1870	0
1871	0
1872	0
1873	0
1874	0
1875	0
1876	0
1877	0
1878	0
1879	0
1880	0
1881	1
1882	0
1883	1
1884	0
1885	0
1886	0
1887	0
1888	1
1889	1
1890	1
1891	0
1892	0
1893	0
1894	1
1895	0
1896	1
1897	1
1898	0
1899	0
1900	1
1901	1
1902	0
1903	1
1904	0
1905	0
1906	0
1907	0
1908	1
1909	1
1910	1
1911	0
1912	0
1913	0
1914	1
1915	0
1916	1
1917	1
1918	0
1919	0
1920	1
1921	1
1922	0
1923	0
1924	0
1925	0
1926	0
1927	0
1928	0
1929	1
1930	0
1931	0
1932	0
1933	0
1934	0
1935	0
1936	0
1937	0
1938	0
1939	0
1940	0
1941	0
1942	0
1943	0
1944	0
1945	0
1946	0
1947	0
1948	0
1949	0
1950	0
1951	0
1952	0
1953	0
1954	0
1955	0
1956	0
1957	0
1958	0
1959	0
1960	0
1961	1
1962	0
1963	0
1964	0
1965	0
1966	0
1967	0
1968	0
1969	1
1970	0
1971	0
1972	0
1973	0
1974	1
1975	0
1976	0
1977	0
1978	0
1979	0
1980	1
1981	1
1982	0
1983	0
1984	0
1985	0
1986	0
1987	0
1988	1
1989	1
1990	0
1991	0
1992	0
1993	0
1994	1
1995	0
1996	1
1997	0
1998	0
1999	0
2000	0
2001	1
2002	0
2003	1
2004	0
2005	0
2006	0
2007	0
2008	1
2009	1
2010	1
2011	0
2012	0
2013	0
2014	1
2015	0
2016	1
2017	1
2018	0
2019	0
2020	1
2021	1
2022	0
2023	1
2024	0
2025	0
2026	0
2027	0
2028	1
2029	1
2030	1
2031	0
2032	0
2033	0
2034	1
2035	0
2036	1
2037	1
2038	0
2039	0
2040	1
2041	0
2042	0
2043	0
2044	0
2045	0
2046	0
2047	0
2048	0
2049	0
2050	0
2051	0
2052	0
2053	0
2054	0
2055	0
2056	0
2057	0
2058	0
2059	0
2060	0
2061	1
2062	0
2063	1
2064	0
2065	0
2066	0
2067	0
2068	1
2069	1
2070	1
2071	0
2072	0
2073	0
2074	1
2075	0
2076	1
2077	1
2078	0
2079	0
2080	1
2081	1
2082	0
2083	1
2084	0
2085	0
2086	0
2087	0
2088	1
2089	1
2090	1
2091	0
2092	0
2093	0
2094	1
2095	0
2096	1
2097	1
2098	0
2099	0
2100	1
2101	1
2102	0
2103	1
2104	0
2105	0
2106	0
2107	0
2108	1
2109	1
2110	1
2111	0
2112	0
2113	0
2114	1
2115	0
2116	1
2117	1
2118	0
2119	0
2120	1
2121	1
2122	0
2123	1
2124	0
2125	0
2126	0
2127	0
2128	1
2129	1
2130	1
2131	0
2132	0
2133	0
2134	1
2135	0
2136	1
2137	1
2138	0
2139	0
2140	1
2141	1
2142	0
2143	1
2144	0
2145	0
2146	0
2147	0
2148	1
2149	1
2150	1
2151	0
2152	0
2153	0
2154	1
2155	0
2156	1
2157	1
2158	0
2159	0
2160	1
2161	1
2162	0
2163	1
2164	0
2165	0
2166	0
2167	0
2168	1
2169	1
2170	1
2171	0
2172	0
2173	0
2174	1
2175	0
2176	1
2177	1
2178	0
2179	0
2180	1
2181	1
2182	0
2183	0
2184	0
2185	0
2186	0
2187	0
2188	0
2189	0
2190	1
2191	0
2192	0
2193	0
2194	0
2195	0
2196	0
2197	0
2198	0
2199	0
2200	0
2201	0
2202	0
2203	0
2204	0
2205	0
2206	0
2207	0
2208	0
2209	0
2210	0
2211	0
2212	0
2213	0
2214	0
2215	0
2216	0
2217	0
2218	0
2219	0
2220	0
2221	0
2222	0
2223	0
2224	0
2225	0
2226	0
2227	0
2228	0
2229	0
2230	0
2231	0
2232	0
2233	0
2234	0
2235	0
2236	0
2237	0
2238	0
2239	0
2240	0
2241	0
2242	0
2243	0
2244	0
2245	0
2246	0
2247	0
2248	0
2249	0
2250	0
2251	0
2252	0
2253	0
2254	0
2255	0
2256	0
2257	0
2258	0
2259	0
2260	0
2261	0
2262	0
2263	1
2264	0
2265	0
2266	0
2267	0
2268	0
2269	1
2270	0
2271	0
2272	0
2273	0
2274	1
2275	0
2276	0
2277	0
2278	0
2279	0
2280	0
2281	1
2282	0
2283	0
2284	0
2285	0
2286	0
2287	0
2288	1
2289	1
2290	1
2291	0
2292	0
2293	0
2294	1
2295	0
2296	0
2297	1
2298	0
2299	0
2300	1
2301	0
2302	0
2303	0
2304	0
2305	0
2306	0
2307	0
2308	1
2309	0
2310	1
2311	0
2312	0
2313	0
2314	0
2315	0
2316	0
2317	1
2318	0
2319	0
2320	0
2321	0
2322	0
2323	0
2324	0
2325	0
2326	0
2327	0
2328	0
2329	0
2330	0
2331	0
2332	0
2333	0
2334	0
2335	0
2336	0
2337	0
2338	0
2339	0
2340	0
2341	0
2342	0
2343	0
2344	0
2345	0
2346	0
2347	0
2348	0
2349	0
2350	0
2351	0
2352	0
2353	0
2354	0
2355	0
2356	0
2357	0
2358	0
2359	0
2360	0
2361	0
2362	0
2363	0
2364	0
2365	0
2366	0
2367	0
2368	0
2369	0
2370	0
2371	0
2372	0
2373	0
2374	0
2375	0
2376	1
2377	0
2378	0
2379	0
2380	0
2381	0
2382	0
2383	0
2384	0
2385	0
2386	0
2387	0
2388	0
2389	0
2390	0
2391	0
2392	0
2393	0
2394	0
2395	0
2396	0
2397	0
2398	0
2399	0
2400	0
2401	0
2402	0
2403	0
2404	0
2405	0
2406	0
2407	0
2408	0
2409	0
2410	0
2411	0
2412	0
2413	0
2414	0
2415	0
2416	0
2417	0
2418	0
2419	0
2420	0
2421	0
2422	0
2423	1
2424	0
2425	0
2426	0
2427	0
2428	1
2429	0
2430	1
2431	0
2432	0
2433	0
2434	1
2435	0
2436	1
2437	1
2438	0
2439	0
2440	1
2441	0
2442	0
2443	1
2444	0
2445	0
2446	0
2447	0
2448	1
2449	0
2450	1
2451	0
2452	0
2453	0
2454	1
2455	0
2456	1
2457	1
2458	0
2459	0
2460	1
2461	0
2462	0
2463	1
2464	0
2465	0
2466	0
2467	0
2468	1
2469	0
2470	0
2471	0
2472	0
2473	0
2474	1
2475	0
2476	0
2477	1
2478	0
2479	0
2480	1
2481	1
2482	0
2483	0
2484	0
2485	0
2486	0
2487	0
2488	0
2489	0
2490	0
2491	0
2492	0
2493	0
2494	0
2495	0
2496	0
2497	0
2498	0
2499	0
2500	0
2501	0
2502	0
2503	0
2504	0
2505	0
2506	0
2507	0
2508	0
2509	0
2510	0
2511	0
2512	0
2513	0
2514	0
2515	0
2516	0
2517	0
2518	0
2519	0
2520	0
2521	0
2522	0
2523	0
2524	0
2525	0
2526	0
2527	0
2528	0
2529	0
2530	0
2531	0
2532	0
2533	0
2534	0
2535	0
2536	0
2537	0
2538	0
2539	0
2540	0
2541	0
2542	0
2543	0
2544	0
2545	0
2546	0
2547	0
2548	0
2549	0
2550	0
2551	0
2552	0
2553	0
2554	0
2555	0
2556	0
2557	0
2558	0
2559	0
2560	0
2561	0
2562	0
2563	0
2564	0
2565	0
2566	0
2567	0
2568	0
2569	0
2570	0
2571	0
2572	0
2573	0
2574	0
2575	0
2576	0
2577	0
2578	0
2579	0
2580	0
2581	0
2582	0
2583	0
2584	0
2585	0
2586	0
2587	0
2588	0
2589	0
2590	0
2591	0
2592	0
2593	0
2594	0
2595	0
2596	0
2597	0
2598	0
2599	0
2600	0
2601	0
2602	0
2603	0
2604	0
2605	0
2606	0
2607	0
2608	0
2609	0
2610	0
2611	0
2612	0
2613	0
2614	0
2615	0
2616	0
2617	0
2618	0
2619	0
2620	0
2621	0
2622	0
2623	0
2624	0
2625	0
2626	0
2627	0
2628	0
2629	0
2630	0
2631	0
2632	0
2633	0
2634	0
2635	0
2636	0
2637	0
2638	0
2639	0
2640	0
2641	0
2642	0
2643	0
2644	0
2645	0
2646	0
2647	0
2648	0
2649	0
2650	0
2651	0
2652	0
2653	0
2654	0
2655	0
2656	0
2657	0
2658	0
2659	0
2660	0
2661	0
2662	0
2663	0
2664	0
2665	0
2666	0
2667	0
2668	0
2669	0
2670	0
2671	0
2672	0
2673	0
2674	0
2675	0
2676	0
2677	0
2678	0
2679	0
2680	0
2681	0
2682	0
2683	0
2684	0
2685	0
2686	0
2687	0
2688	0
2689	0
2690	0
2691	0
2692	0
2693	0
2694	0
2695	0
2696	0
2697	0
2698	0
2699	0
2700	0
2701	0
2702	0
2703	0
2704	0
2705	0
2706	0
2707	0
2708	0
2709	0
2710	0
2711	0
2712	0
2713	0
2714	1
2715	0
2716	0
2717	1
2718	0
2719	0
2720	0
2721	0
2722	0
2723	0
2724	0
2725	0
2726	0
2727	0
2728	0
2729	0
2730	0
2731	0
2732	0
2733	0
2734	0
2735	0
2736	0
2737	0
2738	0
2739	0
2740	0
2741	0
2742	0
2743	0
2744	0
2745	0
2746	0
2747	0
2748	0
2749	0
2750	0
2751	0
2752	0
2753	0
2754	0
2755	0
2756	0
2757	0
2758	0
2759	0
2760	0
2761	1
2762	0
2763	1
2764	0
2765	0
2766	0
2767	0
2768	1
2769	1
2770	1
2771	0
2772	0
2773	0
2774	1
2775	0
2776	1
2777	1
2778	0
2779	0
2780	1
2781	0
2782	0
2783	0
2784	0
2785	0
2786	0
2787	0
2788	0
2789	1
2790	0
2791	0
2792	0
2793	0
2794	0
2795	0
2796	0
2797	0
2798	0
2799	0
2800	0
2801	0
2802	0
2803	0
2804	0
2805	0
2806	0
2807	0
2808	0
2809	0
2810	0
2811	0
2812	0
2813	0
2814	0
2815	0
2816	0
2817	0
2818	0
2819	0
2820	0
2821	0
2822	0
2823	0
2824	0
2825	0
2826	0
2827	0
2828	0
2829	0
2830	0
2831	0
2832	0
2833	0
2834	0
2835	0
2836	0
2837	0
2838	0
2839	0
2840	0
2841	0
2842	0
2843	0
2844	0
2845	0
2846	0
2847	0
2848	0
2849	0
2850	0
2851	0
2852	0
2853	0
2854	0
2855	0
2856	0
2857	0
2858	0
2859	0
2860	0
2861	0
2862	0
2863	0
2864	0
2865	0
2866	0
2867	0
2868	0
2869	0
2870	0
2871	0
2872	0
2873	0
2874	0
2875	0
2876	0
2877	0
2878	0
2879	0
2880	0
2881	0
2882	0
2883	0
2884	0
2885	0
2886	0
2887	0
2888	0
2889	0
2890	0
2891	0
2892	0
2893	0
2894	0
2895	0
2896	0
2897	0
2898	0
2899	0
2900	0
2901	1
2902	0
2903	1
2904	0
2905	0
2906	0
2907	0
2908	1
2909	1
2910	1
2911	0
2912	0
2913	0
2914	1
2915	0
2916	1
2917	1
2918	0
2919	0
2920	1
2921	0
2922	0
2923	0
2924	0
2925	0
2926	0
2927	0
2928	0
2929	0
2930	0
2931	0
2932	0
2933	0
2934	0
2935	0
2936	0
2937	0
2938	0
2939	0
2940	0
2941	1
2942	0
2943	1
2944	0
2945	0
2946	0
2947	0
2948	1
2949	1
2950	1
2951	0
2952	0
2953	0
2954	1
2955	0
2956	1
2957	1
2958	0
2959	0
2960	1
2961	0
2962	0
2963	0
2964	0
2965	0
2966	0
2967	0
2968	0
2969	0
2970	0
2971	0
2972	0
2973	0
2974	0
2975	0
2976	0
2977	0
2978	0
2979	0
2980	0
2981	0
2982	0
2983	0
2984	0
2985	0
2986	0
2987	0
2988	0
2989	0
2990	0
2991	0
2992	0
2993	0
2994	0
2995	0
2996	0
2997	0
2998	0
2999	0
3000	0
3001	0
3002	0
3003	0
3004	0
3005	0
3006	0
3007	0
3008	0
3009	0
3010	0
3011	0
3012	0
3013	0
3014	0
3015	0
3016	0
3017	0
3018	0
3019	0
3020	0
3021	0
3022	0
3023	0
3024	0
3025	0
3026	0
3027	0
3028	1
3029	0
3030	0
3031	0
3032	0
3033	0
3034	0
3035	0
3036	0
3037	0
3038	0
3039	0
3040	0
3041	0
3042	0
3043	0
3044	0
3045	0
3046	0
3047	0
3048	0
3049	0
3050	1
3051	0
3052	0
3053	0
3054	0
3055	0
3056	0
3057	0
3058	0
3059	0
3060	0
3061	0
3062	0
3063	0
3064	0
3065	0
3066	0
3067	0
3068	0
3069	0
3070	0
3071	0
3072	0
3073	0
3074	0
3075	0
3076	0
3077	0
3078	0
3079	0
3080	0
3081	1
3082	0
3083	1
3084	0
3085	0
3086	0
3087	0
3088	1
3089	1
3090	1
3091	0
3092	0
3093	0
3094	1
3095	0
3096	1
3097	1
3098	0
3099	0
3100	1
3101	0
3102	0
3103	0
3104	0
3105	0
3106	0
3107	0
3108	0
3109	0
3110	0
3111	0
3112	0
3113	0
3114	0
3115	0
3116	0
3117	0
3118	0
3119	0
3120	0
3121	0
3122	0
3123	0
3124	0
3125	0
3126	0
3127	0
3128	0
3129	0
3130	0
3131	0
3132	0
3133	0
3134	0
3135	0
3136	0
3137	0
3138	0
3139	0
3140	0
3141	0
3142	0
3143	0
3144	0
3145	0
3146	0
3147	0
3148	0
3149	1
3150	0
3151	0
3152	0
3153	0
3154	0
3155	0
3156	0
3157	0
3158	0
3159	0
3160	0
3161	0
3162	0
3163	0
3164	0
3165	0
3166	0
3167	0
3168	0
3169	0
3170	0
3171	0
3172	0
3173	0
3174	0
3175	0
3176	0
3177	0
3178	0
3179	0
3180	0
3181	0
3182	0
3183	0
3184	0
3185	0
3186	0
3187	0
3188	0
3189	0
3190	0
3191	0
3192	0
3193	0
3194	0
3195	0
3196	0
3197	0
3198	0
3199	0
3200	0
3201	0
3202	0
3203	0
3204	0
3205	0
3206	0
3207	0
3208	0
3209	0
3210	0
3211	0
3212	0
3213	0
3214	0
3215	0
3216	0
3217	0
3218	0
3219	0
3220	0
3221	0
3222	0
3223	0
3224	0
3225	0
3226	0
3227	0
3228	0
3229	0
3230	0
3231	0
3232	0
3233	0
3234	0
3235	0
3236	0
3237	0
3238	0
3239	0
3240	0
3241	1
3242	0
3243	1
3244	0
3245	0
3246	0
3247	0
3248	1
3249	1
3250	1
3251	0
3252	0
3253	0
3254	1
3255	0
3256	1
3257	1
3258	0
3259	0
3260	1
3261	1
3262	0
3263	1
3264	0
3265	0
3266	0
3267	0
3268	1
3269	1
3270	1
3271	0
3272	0
3273	0
3274	1
3275	0
3276	1
3277	1
3278	0
3279	0
3280	1
3281	0
3282	0
3283	0
3284	0
3285	0
3286	0
3287	0
3288	0
3289	0
3290	0
3291	0
3292	0
3293	0
3294	0
3295	0
3296	0
3297	0
3298	0
3299	0
3300	0
3301	0
3302	0
3303	0
3304	0
3305	0
3306	0
3307	0
3308	0
3309	0
3310	0
3311	0
3312	0
3313	0
3314	0
3315	0
3316	0
3317	0
3318	0
3319	0
3320	0
3321	0
3322	0
3323	0
3324	0
3325	0
3326	0
3327	0
3328	0
3329	0
3330	0
3331	0
3332	0
3333	0
3334	0
3335	0
3336	0
3337	0
3338	0
3339	0
3340	0
3341	0
3342	0
3343	0
3344	0
3345	0
3346	0
3347	0
3348	0
3349	0
3350	0
3351	0
3352	0
3353	0
3354	0
3355	0
3356	0
3357	0
3358	0
3359	0
3360	0
3361	0
3362	0
3363	0
3364	0
3365	0
3366	0
3367	0
3368	0
3369	0
3370	0
3371	0
3372	0
3373	0
3374	0
3375	0
3376	0
3377	0
3378	0
3379	0
3380	0
3381	1
3382	0
3383	1
3384	0
3385	0
3386	0
3387	0
3388	1
3389	0
3390	1
3391	0
3392	0
3393	0
3394	1
3395	0
3396	1
3397	1
3398	0
3399	0
3400	1
3401	1
3402	0
3403	1
3404	0
3405	0
3406	0
3407	0
3408	1
3409	1
3410	1
3411	0
3412	0
3413	0
3414	1
3415	0
3416	1
3417	1
3418	0
3419	0
3420	1
3421	0
3422	0
3423	1
3424	0
3425	0
3426	0
3427	0
3428	1
3429	1
3430	1
3431	0
3432	0
3433	0
3434	1
3435	0
3436	1
3437	1
3438	0
3439	0
3440	1
3441	0
3442	0
3443	1
3444	0
3445	0
3446	0
3447	0
3448	1
3449	0
3450	0
3451	0
3452	0
3453	0
3454	0
3455	0
3456	0
3457	1
3458	0
3459	0
3460	1
3461	0
3462	0
3463	0
3464	0
3465	0
3466	0
3467	0
3468	0
3469	0
3470	0
3471	0
3472	0
3473	0
3474	0
3475	0
3476	0
3477	0
3478	0
3479	0
3480	0
3481	0
3482	0
3483	0
3484	0
3485	0
3486	0
3487	0
3488	0
3489	0
3490	0
3491	0
3492	0
3493	0
3494	0
3495	0
3496	0
3497	0
3498	0
3499	0
3500	0
3501	0
3502	0
3503	0
3504	0
3505	0
3506	0
3507	0
3508	0
3509	0
3510	0
3511	0
3512	0
3513	0
3514	0
3515	0
3516	0
3517	0
3518	0
3519	0
3520	0
3521	1
3522	0
3523	1
3524	0
3525	0
3526	0
3527	0
3528	1
3529	1
3530	1
3531	0
3532	0
3533	0
3534	1
3535	0
3536	0
3537	1
3538	0
3539	0
3540	0
3541	0
3542	0
3543	0
3544	0
3545	0
3546	0
3547	0
3548	0
3549	1
3550	0
3551	0
3552	0
3553	0
3554	0
3555	0
3556	1
3557	1
3558	0
3559	0
3560	1
3561	1
3562	0
3563	1
3564	0
3565	0
3566	0
3567	0
3568	1
3569	0
3570	1
3571	0
3572	0
3573	0
3574	1
3575	0
3576	1
3577	0
3578	0
3579	0
3580	1
3581	0
3582	0
3583	0
3584	0
3585	0
3586	0
3587	0
3588	0
3589	0
3590	0
3591	0
3592	0
3593	0
3594	0
3595	0
3596	0
3597	0
3598	0
3599	0
3600	0
3601	0
3602	0
3603	0
3604	0
3605	0
3606	0
3607	0
3608	0
3609	0
3610	0
3611	0
3612	0
3613	0
3614	0
3615	0
3616	0
3617	0
3618	0
3619	0
3620	0
3621	0
3622	0
3623	0
3624	0
3625	0
3626	0
3627	0
3628	0
3629	0
3630	0
3631	0
3632	0
3633	0
3634	0
3635	0
3636	0
3637	0
3638	0
3639	0
3640	0
3641	0
3642	0
3643	0
3644	0
3645	0
3646	0
3647	0
3648	0
3649	0
3650	0
3651	0
3652	0
3653	0
3654	0
3655	0
3656	0
3657	0
3658	0
3659	0
3660	0
3661	0
3662	0
3663	0
3664	0
3665	0
3666	0
3667	0
3668	0
3669	0
3670	0
3671	0
3672	0
3673	0
3674	0
3675	0
3676	0
3677	0
3678	0
3679	0
3680	0
3681	0
3682	0
3683	0
3684	0
3685	0
3686	0
3687	0
3688	0
3689	0
3690	0
3691	0
3692	0
3693	0
3694	0
3695	0
3696	0
3697	0
3698	0
3699	0
3700	0
3701	1
3702	0
3703	1
3704	0
3705	0
3706	0
3707	0
3708	1
3709	1
3710	1
3711	0
3712	0
3713	0
3714	1
3715	0
3716	1
3717	1
3718	0
3719	0
3720	1
3721	1
3722	0
3723	0
3724	0
3725	0
3726	0
3727	0
3728	1
3729	1
3730	1
3731	0
3732	0
3733	0
3734	1
3735	0
3736	1
3737	1
3738	0
3739	0
3740	1
3741	0
3742	0
3743	0
3744	0
3745	0
3746	0
3747	0
3748	0
3749	0
3750	0
3751	0
3752	0
3753	0
3754	0
3755	0
3756	0
3757	0
3758	0
3759	0
3760	0
3761	0
3762	0
3763	0
3764	0
3765	0
3766	0
3767	0
3768	0
3769	0
3770	0
3771	0
3772	0
3773	0
3774	0
3775	0
3776	0
3777	0
3778	0
3779	0
3780	0
3781	1
3782	0
3783	1
3784	0
3785	0
3786	0
3787	0
3788	1
3789	0
3790	1
3791	0
3792	0
3793	0
3794	1
3795	0
3796	1
3797	1
3798	0
3799	0
3800	1
3801	0
3802	0
3803	0
3804	0
3805	0
3806	0
3807	0
3808	0
3809	0
3810	0
3811	0
3812	0
3813	0
3814	0
3815	0
3816	0
3817	0
3818	0
3819	0
3820	0
3821	0
3822	0
3823	0
3824	0
3825	0
3826	0
3827	0
3828	0
3829	0
3830	0
3831	0
3832	0
3833	0
3834	0
3835	0
3836	0
3837	0
3838	0
3839	0
3840	0
3841	0
3842	0
3843	1
3844	0
3845	0
3846	0
3847	0
3848	1
3849	0
3850	1
3851	0
3852	0
3853	0
3854	1
3855	0
3856	1
3857	1
3858	0
3859	0
3860	1
3861	1
3862	0
3863	1
3864	0
3865	0
3866	0
3867	0
3868	1
3869	1
3870	1
3871	0
3872	0
3873	0
3874	1
3875	0
3876	1
3877	1
3878	0
3879	0
3880	1
3881	0
3882	0
3883	1
3884	0
3885	0
3886	0
3887	0
3888	1
3889	0
3890	1
3891	0
3892	0
3893	0
3894	0
3895	0
3896	1
3897	1
3898	0
3899	0
3900	0
3901	0
3902	0
3903	1
3904	0
3905	0
3906	0
3907	0
3908	0
3909	0
3910	1
3911	0
3912	0
3913	0
3914	0
3915	0
3916	0
3917	1
3918	0
3919	0
3920	1
3921	0
3922	0
3923	0
3924	0
3925	0
3926	0
3927	0
3928	0
3929	0
3930	0
3931	0
3932	0
3933	0
3934	0
3935	0
3936	0
3937	0
3938	0
3939	0
3940	0
3941	0
3942	0
3943	0
3944	0
3945	0
3946	0
3947	0
3948	0
3949	0
3950	0
3951	0
3952	0
3953	0
3954	0
3955	0
3956	0
3957	0
3958	0
3959	0
3960	0
3961	1
3962	0
3963	1
3964	0
3965	0
3966	0
3967	0
3968	1
3969	1
3970	1
3971	0
3972	0
3973	0
3974	1
3975	0
3976	1
3977	1
3978	0
3979	0
3980	1
3981	0
3982	0
3983	0
3984	0
3985	0
3986	0
3987	0
3988	0
3989	0
3990	0
3991	0
3992	0
3993	0
3994	0
3995	0
3996	0
3997	0
3998	0
3999	0
4000	0
4001	0
4002	0
4003	0
4004	0
4005	0
4006	0
4007	0
4008	0
4009	0
4010	0
4011	0
4012	0
4013	0
4014	0
4015	0
4016	0
4017	0
4018	0
4019	0
4020	0
4021	0
4022	0
4023	0
4024	0
4025	0
4026	0
4027	0
4028	0
4029	0
4030	0
4031	0
4032	0
4033	0
4034	0
4035	0
4036	0
4037	0
4038	0
4039	0
4040	0
4041	0
4042	0
4043	0
4044	0
4045	0
4046	0
4047	0
4048	0
4049	0
4050	0
4051	0
4052	0
4053	0
4054	0
4055	0
4056	0
4057	0
4058	0
4059	0
4060	0
4061	0
4062	0
4063	0
4064	0
4065	0
4066	0
4067	0
4068	0
4069	0
4070	0
4071	0
4072	0
4073	0
4074	0
4075	0
4076	0
4077	0
4078	0
4079	0
4080	0
4081	0
4082	0
4083	0
4084	0
4085	0
4086	0
4087	0
4088	0
4089	0
4090	0
4091	0
4092	0
4093	0
4094	0
4095	0
4096	0
4097	0
4098	0
4099	0
4100	0
4101	0
4102	0
4103	1
4104	0
4105	0
4106	0
4107	0
4108	1
4109	1
4110	0
4111	0
4112	0
4113	0
4114	1
4115	0
4116	1
4117	1
4118	0
4119	0
4120	1
75242	0
75243	0
75244	1
75245	0
75246	0
75247	0
75248	0
75249	0
75250	1
75251	1
75252	0
75253	0
75254	0
75255	0
75256	0
75257	0
75258	0
75259	0
75260	0
75261	0
75262	0
75263	0
75264	0
75265	0
75266	0
75267	0
75268	0
75269	0
75270	0
75271	0
75272	1
75273	0
75274	0
75275	1
75276	1
75277	0
75278	0
75279	1
75280	0
75281	0
75282	0
75283	0
75284	0
75285	0
75286	0
75287	0
75288	0
75289	0
75290	0
75291	0
75292	0
75293	0
75294	1
75295	1
75296	0
75297	0
75298	0
75299	0
75300	0
75301	0
75302	0
75303	1
75304	0
75305	0
75306	0
75307	1
75308	0
75309	0
75310	0
75311	0
75312	0
75313	0
75314	0
75315	0
75316	0
75317	0
75318	0
75319	1
75320	0
75321	0
75322	0
75323	1
75324	0
75325	0
75326	0
75327	0
75328	0
75329	0
75330	0
75331	1
75332	0
75333	0
75334	0
75335	0
75336	0
75337	0
75338	0
75339	0
75340	0
75341	0
75342	0
75343	0
75344	0
75345	0
75346	0
75347	0
75348	0
75349	0
75350	0
75351	1
75352	0
75353	0
75354	0
75355	1
75356	0
75357	0
75358	0
75359	1
75360	0
75361	0
75362	0
75363	0
75364	0
75365	0
75366	0
75367	0
75368	0
75369	0
75370	0
75371	0
75372	0
75373	0
75374	0
75375	1
75376	0
75377	0
75378	0
75379	0
75380	0
75381	0
75382	0
75383	1
75384	0
75385	0
75386	0
75387	1
75388	0
75389	0
75390	0
75391	0
75392	0
75393	0
75394	0
75395	0
75396	0
75397	0
75398	0
75399	1
75400	0
75401	0
75402	0
75403	1
75404	0
75405	0
75406	0
75407	0
75408	0
75409	0
75410	0
75411	1
75412	0
75413	0
75414	0
75415	0
75416	0
75417	0
75418	0
75419	0
75420	0
75421	0
75422	0
75423	0
75424	0
75425	0
75426	0
75427	0
75428	0
75429	0
75430	0
75431	1
75432	0
75433	0
75434	0
75435	1
75436	0
75437	0
75438	0
75439	1
75440	0
75441	0
75442	0
75443	0
75444	0
75445	0
75446	0
75447	0
75448	0
75449	0
75450	0
75451	0
75452	0
75453	0
75454	0
75455	1
75456	0
75457	0
75458	0
75459	0
75460	0
75461	0
75462	0
75463	1
75464	0
75465	0
75466	0
75467	1
75468	0
75469	0
75470	0
75471	0
75472	0
75473	0
75474	0
75475	0
75476	0
75477	0
75478	0
75479	1
75480	0
75481	0
""")
    resource20("checkpoint/FIX17_EXTRACTED_SCENARIO.tsv","fa3561a3dc353c0bd1a22dfd02b6870aec533c4081f470fceb00607e073ac3c3","""component	index	value
beta_pv_minus	1,1	0.0
beta_pv_minus	2,1	0.0
beta_pv_minus	3,1	0.0
beta_pv_minus	4,1	0.0
beta_pv_minus	5,1	0.0
beta_pv_minus	1,2	0.0
beta_pv_minus	2,2	0.0
beta_pv_minus	3,2	0.0
beta_pv_minus	4,2	0.0
beta_pv_minus	5,2	0.0
beta_pv_minus	1,3	0.0
beta_pv_minus	2,3	0.0
beta_pv_minus	3,3	0.0
beta_pv_minus	4,3	0.0
beta_pv_minus	5,3	0.0
beta_pv_minus	1,4	0.0
beta_pv_minus	2,4	0.0
beta_pv_minus	3,4	0.0
beta_pv_minus	4,4	0.0
beta_pv_minus	5,4	0.0
beta_pv_minus	1,5	0.0
beta_pv_minus	2,5	0.0
beta_pv_minus	3,5	0.0
beta_pv_minus	4,5	0.0
beta_pv_minus	5,5	0.0
beta_pv_minus	1,6	0.0
beta_pv_minus	2,6	0.0
beta_pv_minus	3,6	0.0
beta_pv_minus	4,6	0.0
beta_pv_minus	5,6	0.0
beta_pv_minus	1,7	-0.0
beta_pv_minus	2,7	-0.0
beta_pv_minus	3,7	-0.0
beta_pv_minus	4,7	-0.0
beta_pv_minus	5,7	-0.0
beta_pv_minus	1,8	-0.0
beta_pv_minus	2,8	-0.0
beta_pv_minus	3,8	-0.0
beta_pv_minus	4,8	-0.0
beta_pv_minus	5,8	-0.0
beta_pv_minus	1,9	-0.0
beta_pv_minus	2,9	-0.0
beta_pv_minus	3,9	-0.0
beta_pv_minus	4,9	-0.0
beta_pv_minus	5,9	-0.0
beta_pv_minus	1,10	-0.0
beta_pv_minus	2,10	-0.0
beta_pv_minus	3,10	-0.0
beta_pv_minus	4,10	-0.0
beta_pv_minus	5,10	-0.0
beta_pv_minus	1,11	-0.0
beta_pv_minus	2,11	-0.0
beta_pv_minus	3,11	-0.0
beta_pv_minus	4,11	-0.0
beta_pv_minus	5,11	-0.0
beta_pv_minus	1,12	-0.0
beta_pv_minus	2,12	-0.0
beta_pv_minus	3,12	-0.0
beta_pv_minus	4,12	-0.0
beta_pv_minus	5,12	-0.0
beta_pv_minus	1,13	-0.0
beta_pv_minus	2,13	-0.0
beta_pv_minus	3,13	-0.0
beta_pv_minus	4,13	-0.0
beta_pv_minus	5,13	-0.0
beta_pv_minus	1,14	-0.0
beta_pv_minus	2,14	-0.0
beta_pv_minus	3,14	-0.0
beta_pv_minus	4,14	-0.0
beta_pv_minus	5,14	-0.0
beta_pv_minus	1,15	-0.0
beta_pv_minus	2,15	-0.0
beta_pv_minus	3,15	-0.0
beta_pv_minus	4,15	-0.0
beta_pv_minus	5,15	-0.0
beta_pv_minus	1,16	-0.0
beta_pv_minus	2,16	-0.0
beta_pv_minus	3,16	-0.0
beta_pv_minus	4,16	-0.0
beta_pv_minus	5,16	-0.0
beta_pv_minus	1,17	-0.0
beta_pv_minus	2,17	-0.0
beta_pv_minus	3,17	-0.0
beta_pv_minus	4,17	-0.0
beta_pv_minus	5,17	-0.0
beta_pv_minus	1,18	-0.0
beta_pv_minus	2,18	-0.0
beta_pv_minus	3,18	-0.0
beta_pv_minus	4,18	-0.0
beta_pv_minus	5,18	-0.0
beta_pv_minus	1,19	-0.0
beta_pv_minus	2,19	-0.0
beta_pv_minus	3,19	-0.0
beta_pv_minus	4,19	-0.0
beta_pv_minus	5,19	-0.0
beta_pv_minus	1,20	-0.0
beta_pv_minus	2,20	-0.0
beta_pv_minus	3,20	-0.0
beta_pv_minus	4,20	-0.0
beta_pv_minus	5,20	-0.0
beta_pv_minus	1,21	0.0
beta_pv_minus	2,21	0.0
beta_pv_minus	3,21	0.0
beta_pv_minus	4,21	0.0
beta_pv_minus	5,21	0.0
beta_pv_minus	1,22	0.0
beta_pv_minus	2,22	0.0
beta_pv_minus	3,22	0.0
beta_pv_minus	4,22	0.0
beta_pv_minus	5,22	0.0
beta_pv_minus	1,23	0.0
beta_pv_minus	2,23	0.0
beta_pv_minus	3,23	0.0
beta_pv_minus	4,23	0.0
beta_pv_minus	5,23	0.0
beta_pv_minus	1,24	0.0
beta_pv_minus	2,24	0.0
beta_pv_minus	3,24	0.0
beta_pv_minus	4,24	0.0
beta_pv_minus	5,24	0.0
beta_pv_minus	1,25	0.0
beta_pv_minus	2,25	0.0
beta_pv_minus	3,25	0.0
beta_pv_minus	4,25	0.0
beta_pv_minus	5,25	0.0
beta_pv_minus	1,26	0.0
beta_pv_minus	2,26	0.0
beta_pv_minus	3,26	0.0
beta_pv_minus	4,26	0.0
beta_pv_minus	5,26	0.0
beta_pv_minus	1,27	0.0
beta_pv_minus	2,27	0.0
beta_pv_minus	3,27	0.0
beta_pv_minus	4,27	0.0
beta_pv_minus	5,27	0.0
beta_pv_minus	1,28	0.0
beta_pv_minus	2,28	0.0
beta_pv_minus	3,28	0.0
beta_pv_minus	4,28	0.0
beta_pv_minus	5,28	0.0
beta_pv_minus	1,29	0.0
beta_pv_minus	2,29	0.0
beta_pv_minus	3,29	0.0
beta_pv_minus	4,29	0.0
beta_pv_minus	5,29	0.0
beta_pv_minus	1,30	0.0
beta_pv_minus	2,30	0.0
beta_pv_minus	3,30	0.0
beta_pv_minus	4,30	0.0
beta_pv_minus	5,30	0.0
beta_pv_minus	1,31	-0.0
beta_pv_minus	2,31	-0.0
beta_pv_minus	3,31	-0.0
beta_pv_minus	4,31	-0.0
beta_pv_minus	5,31	-0.0
beta_pv_minus	1,32	-0.0
beta_pv_minus	2,32	-0.0
beta_pv_minus	3,32	-0.0
beta_pv_minus	4,32	-0.0
beta_pv_minus	5,32	-0.0
beta_pv_minus	1,33	-0.0
beta_pv_minus	2,33	-0.0
beta_pv_minus	3,33	-0.0
beta_pv_minus	4,33	-0.0
beta_pv_minus	5,33	-0.0
beta_pv_minus	1,34	-0.0
beta_pv_minus	2,34	-0.0
beta_pv_minus	3,34	-0.0
beta_pv_minus	4,34	-0.0
beta_pv_minus	5,34	-0.0
beta_pv_minus	1,35	-0.0
beta_pv_minus	2,35	-0.0
beta_pv_minus	3,35	-0.0
beta_pv_minus	4,35	-0.0
beta_pv_minus	5,35	-0.0
beta_pv_minus	1,36	-0.0
beta_pv_minus	2,36	-0.0
beta_pv_minus	3,36	-0.0
beta_pv_minus	4,36	-0.0
beta_pv_minus	5,36	-0.0
beta_pv_minus	1,37	-0.0
beta_pv_minus	2,37	-0.0
beta_pv_minus	3,37	-0.0
beta_pv_minus	4,37	-0.0
beta_pv_minus	5,37	-0.0
beta_pv_minus	1,38	-0.0
beta_pv_minus	2,38	-0.0
beta_pv_minus	3,38	-0.0
beta_pv_minus	4,38	-0.0
beta_pv_minus	5,38	-0.0
beta_pv_minus	1,39	-0.0
beta_pv_minus	2,39	-0.0
beta_pv_minus	3,39	-0.0
beta_pv_minus	4,39	-0.0
beta_pv_minus	5,39	-0.0
beta_pv_minus	1,40	-0.0
beta_pv_minus	2,40	-0.0
beta_pv_minus	3,40	-0.0
beta_pv_minus	4,40	-0.0
beta_pv_minus	5,40	-0.0
beta_pv_minus	1,41	-0.0
beta_pv_minus	2,41	-0.0
beta_pv_minus	3,41	-0.0
beta_pv_minus	4,41	-0.0
beta_pv_minus	5,41	-0.0
beta_pv_minus	1,42	-0.0
beta_pv_minus	2,42	-0.0
beta_pv_minus	3,42	-0.0
beta_pv_minus	4,42	-0.0
beta_pv_minus	5,42	-0.0
beta_pv_minus	1,43	-0.0
beta_pv_minus	2,43	-0.0
beta_pv_minus	3,43	-0.0
beta_pv_minus	4,43	-0.0
beta_pv_minus	5,43	-0.0
beta_pv_minus	1,44	-0.0
beta_pv_minus	2,44	-0.0
beta_pv_minus	3,44	-0.0
beta_pv_minus	4,44	-0.0
beta_pv_minus	5,44	-0.0
beta_pv_minus	1,45	0.0
beta_pv_minus	2,45	0.0
beta_pv_minus	3,45	0.0
beta_pv_minus	4,45	0.0
beta_pv_minus	5,45	0.0
beta_pv_minus	1,46	0.0
beta_pv_minus	2,46	0.0
beta_pv_minus	3,46	0.0
beta_pv_minus	4,46	0.0
beta_pv_minus	5,46	0.0
beta_pv_minus	1,47	0.0
beta_pv_minus	2,47	0.0
beta_pv_minus	3,47	0.0
beta_pv_minus	4,47	0.0
beta_pv_minus	5,47	0.0
beta_pv_minus	1,48	0.0
beta_pv_minus	2,48	0.0
beta_pv_minus	3,48	0.0
beta_pv_minus	4,48	0.0
beta_pv_minus	5,48	0.0
beta_pv_minus	1,49	0.0
beta_pv_minus	2,49	0.0
beta_pv_minus	3,49	0.0
beta_pv_minus	4,49	0.0
beta_pv_minus	5,49	0.0
beta_pv_minus	1,50	0.0
beta_pv_minus	2,50	0.0
beta_pv_minus	3,50	0.0
beta_pv_minus	4,50	0.0
beta_pv_minus	5,50	0.0
beta_pv_minus	1,51	0.0
beta_pv_minus	2,51	0.0
beta_pv_minus	3,51	0.0
beta_pv_minus	4,51	0.0
beta_pv_minus	5,51	0.0
beta_pv_minus	1,52	0.0
beta_pv_minus	2,52	0.0
beta_pv_minus	3,52	0.0
beta_pv_minus	4,52	0.0
beta_pv_minus	5,52	0.0
beta_pv_minus	1,53	0.0
beta_pv_minus	2,53	0.0
beta_pv_minus	3,53	0.0
beta_pv_minus	4,53	0.0
beta_pv_minus	5,53	0.0
beta_pv_minus	1,54	0.0
beta_pv_minus	2,54	0.0
beta_pv_minus	3,54	0.0
beta_pv_minus	4,54	0.0
beta_pv_minus	5,54	0.0
beta_pv_minus	1,55	-0.0
beta_pv_minus	2,55	-0.0
beta_pv_minus	3,55	-0.0
beta_pv_minus	4,55	-0.0
beta_pv_minus	5,55	-0.0
beta_pv_minus	1,56	-0.0
beta_pv_minus	2,56	-0.0
beta_pv_minus	3,56	-0.0
beta_pv_minus	4,56	-0.0
beta_pv_minus	5,56	-0.0
beta_pv_minus	1,57	-0.0
beta_pv_minus	2,57	-0.0
beta_pv_minus	3,57	-0.0
beta_pv_minus	4,57	-0.0
beta_pv_minus	5,57	-0.0
beta_pv_minus	1,58	-0.0
beta_pv_minus	2,58	-0.0
beta_pv_minus	3,58	-0.0
beta_pv_minus	4,58	-0.0
beta_pv_minus	5,58	-0.0
beta_pv_minus	1,59	-0.0
beta_pv_minus	2,59	-0.0
beta_pv_minus	3,59	-0.0
beta_pv_minus	4,59	-0.0
beta_pv_minus	5,59	-0.0
beta_pv_minus	1,60	-0.0
beta_pv_minus	2,60	-0.0
beta_pv_minus	3,60	-0.0
beta_pv_minus	4,60	-0.0
beta_pv_minus	5,60	-0.0
beta_pv_minus	1,61	-0.0
beta_pv_minus	2,61	-0.0
beta_pv_minus	3,61	-0.0
beta_pv_minus	4,61	-0.0
beta_pv_minus	5,61	-0.0
beta_pv_minus	1,62	-0.0
beta_pv_minus	2,62	-0.0
beta_pv_minus	3,62	-0.0
beta_pv_minus	4,62	-0.0
beta_pv_minus	5,62	-0.0
beta_pv_minus	1,63	-0.0
beta_pv_minus	2,63	-0.0
beta_pv_minus	3,63	-0.0
beta_pv_minus	4,63	-0.0
beta_pv_minus	5,63	-0.0
beta_pv_minus	1,64	-0.0
beta_pv_minus	2,64	-0.0
beta_pv_minus	3,64	-0.0
beta_pv_minus	4,64	-0.0
beta_pv_minus	5,64	-0.0
beta_pv_minus	1,65	-0.0
beta_pv_minus	2,65	-0.0
beta_pv_minus	3,65	-0.0
beta_pv_minus	4,65	-0.0
beta_pv_minus	5,65	-0.0
beta_pv_minus	1,66	-0.0
beta_pv_minus	2,66	-0.0
beta_pv_minus	3,66	-0.0
beta_pv_minus	4,66	-0.0
beta_pv_minus	5,66	-0.0
beta_pv_minus	1,67	-0.0
beta_pv_minus	2,67	-0.0
beta_pv_minus	3,67	-0.0
beta_pv_minus	4,67	-0.0
beta_pv_minus	5,67	-0.0
beta_pv_minus	1,68	-0.0
beta_pv_minus	2,68	-0.0
beta_pv_minus	3,68	-0.0
beta_pv_minus	4,68	-0.0
beta_pv_minus	5,68	-0.0
beta_pv_minus	1,69	0.0
beta_pv_minus	2,69	0.0
beta_pv_minus	3,69	0.0
beta_pv_minus	4,69	0.0
beta_pv_minus	5,69	0.0
beta_pv_minus	1,70	0.0
beta_pv_minus	2,70	0.0
beta_pv_minus	3,70	0.0
beta_pv_minus	4,70	0.0
beta_pv_minus	5,70	0.0
beta_pv_minus	1,71	0.0
beta_pv_minus	2,71	0.0
beta_pv_minus	3,71	0.0
beta_pv_minus	4,71	0.0
beta_pv_minus	5,71	0.0
beta_pv_minus	1,72	0.0
beta_pv_minus	2,72	0.0
beta_pv_minus	3,72	0.0
beta_pv_minus	4,72	0.0
beta_pv_minus	5,72	0.0
beta_pv_minus	1,73	0.0
beta_pv_minus	2,73	0.0
beta_pv_minus	3,73	0.0
beta_pv_minus	4,73	0.0
beta_pv_minus	5,73	0.0
beta_pv_minus	1,74	0.0
beta_pv_minus	2,74	0.0
beta_pv_minus	3,74	0.0
beta_pv_minus	4,74	0.0
beta_pv_minus	5,74	0.0
beta_pv_minus	1,75	0.0
beta_pv_minus	2,75	0.0
beta_pv_minus	3,75	0.0
beta_pv_minus	4,75	0.0
beta_pv_minus	5,75	0.0
beta_pv_minus	1,76	0.0
beta_pv_minus	2,76	0.0
beta_pv_minus	3,76	0.0
beta_pv_minus	4,76	0.0
beta_pv_minus	5,76	0.0
beta_pv_minus	1,77	0.0
beta_pv_minus	2,77	0.0
beta_pv_minus	3,77	0.0
beta_pv_minus	4,77	0.0
beta_pv_minus	5,77	0.0
beta_pv_minus	1,78	0.0
beta_pv_minus	2,78	0.0
beta_pv_minus	3,78	0.0
beta_pv_minus	4,78	0.0
beta_pv_minus	5,78	0.0
beta_pv_minus	1,79	-0.0
beta_pv_minus	2,79	-0.0
beta_pv_minus	3,79	-0.0
beta_pv_minus	4,79	-0.0
beta_pv_minus	5,79	-0.0
beta_pv_minus	1,80	-0.0
beta_pv_minus	2,80	-0.0
beta_pv_minus	3,80	-0.0
beta_pv_minus	4,80	-0.0
beta_pv_minus	5,80	-0.0
beta_pv_minus	1,81	-0.0
beta_pv_minus	2,81	-0.0
beta_pv_minus	3,81	-0.0
beta_pv_minus	4,81	-0.0
beta_pv_minus	5,81	-0.0
beta_pv_minus	1,82	-0.0
beta_pv_minus	2,82	-0.0
beta_pv_minus	3,82	-0.0
beta_pv_minus	4,82	-0.0
beta_pv_minus	5,82	-0.0
beta_pv_minus	1,83	-0.0
beta_pv_minus	2,83	-0.0
beta_pv_minus	3,83	-0.0
beta_pv_minus	4,83	-0.0
beta_pv_minus	5,83	-0.0
beta_pv_minus	1,84	-0.0
beta_pv_minus	2,84	-0.0
beta_pv_minus	3,84	-0.0
beta_pv_minus	4,84	-0.0
beta_pv_minus	5,84	-0.0
beta_pv_minus	1,85	-0.0
beta_pv_minus	2,85	-0.0
beta_pv_minus	3,85	-0.0
beta_pv_minus	4,85	-0.0
beta_pv_minus	5,85	-0.0
beta_pv_minus	1,86	-0.0
beta_pv_minus	2,86	-0.0
beta_pv_minus	3,86	-0.0
beta_pv_minus	4,86	-0.0
beta_pv_minus	5,86	-0.0
beta_pv_minus	1,87	-0.0
beta_pv_minus	2,87	-0.0
beta_pv_minus	3,87	-0.0
beta_pv_minus	4,87	-0.0
beta_pv_minus	5,87	-0.0
beta_pv_minus	1,88	-0.0
beta_pv_minus	2,88	-0.0
beta_pv_minus	3,88	-0.0
beta_pv_minus	4,88	-0.0
beta_pv_minus	5,88	-0.0
beta_pv_minus	1,89	-0.0
beta_pv_minus	2,89	-0.0
beta_pv_minus	3,89	-0.0
beta_pv_minus	4,89	-0.0
beta_pv_minus	5,89	-0.0
beta_pv_minus	1,90	-0.0
beta_pv_minus	2,90	-0.0
beta_pv_minus	3,90	-0.0
beta_pv_minus	4,90	-0.0
beta_pv_minus	5,90	-0.0
beta_pv_minus	1,91	-0.0
beta_pv_minus	2,91	-0.0
beta_pv_minus	3,91	-0.0
beta_pv_minus	4,91	-0.0
beta_pv_minus	5,91	-0.0
beta_pv_minus	1,92	-0.0
beta_pv_minus	2,92	-0.0
beta_pv_minus	3,92	-0.0
beta_pv_minus	4,92	-0.0
beta_pv_minus	5,92	-0.0
beta_pv_minus	1,93	0.0
beta_pv_minus	2,93	0.0
beta_pv_minus	3,93	0.0
beta_pv_minus	4,93	0.0
beta_pv_minus	5,93	0.0
beta_pv_minus	1,94	0.0
beta_pv_minus	2,94	0.0
beta_pv_minus	3,94	0.0
beta_pv_minus	4,94	0.0
beta_pv_minus	5,94	0.0
beta_pv_minus	1,95	0.0
beta_pv_minus	2,95	0.0
beta_pv_minus	3,95	0.0
beta_pv_minus	4,95	0.0
beta_pv_minus	5,95	0.0
beta_pv_minus	1,96	0.0
beta_pv_minus	2,96	0.0
beta_pv_minus	3,96	0.0
beta_pv_minus	4,96	0.0
beta_pv_minus	5,96	0.0
beta_pv_plus	1,1	0.0
beta_pv_plus	2,1	0.0
beta_pv_plus	3,1	0.0
beta_pv_plus	4,1	0.0
beta_pv_plus	5,1	0.0
beta_pv_plus	1,2	0.0
beta_pv_plus	2,2	0.0
beta_pv_plus	3,2	0.0
beta_pv_plus	4,2	0.0
beta_pv_plus	5,2	0.0
beta_pv_plus	1,3	0.0
beta_pv_plus	2,3	0.0
beta_pv_plus	3,3	0.0
beta_pv_plus	4,3	0.0
beta_pv_plus	5,3	0.0
beta_pv_plus	1,4	0.0
beta_pv_plus	2,4	0.0
beta_pv_plus	3,4	0.0
beta_pv_plus	4,4	0.0
beta_pv_plus	5,4	0.0
beta_pv_plus	1,5	0.0
beta_pv_plus	2,5	0.0
beta_pv_plus	3,5	0.0
beta_pv_plus	4,5	0.0
beta_pv_plus	5,5	0.0
beta_pv_plus	1,6	0.0
beta_pv_plus	2,6	0.0
beta_pv_plus	3,6	0.0
beta_pv_plus	4,6	0.0
beta_pv_plus	5,6	0.0
beta_pv_plus	1,7	1.0
beta_pv_plus	2,7	1.0
beta_pv_plus	3,7	1.0
beta_pv_plus	4,7	1.0
beta_pv_plus	5,7	1.0
beta_pv_plus	1,8	1.0
beta_pv_plus	2,8	1.0
beta_pv_plus	3,8	1.0
beta_pv_plus	4,8	1.0
beta_pv_plus	5,8	1.0
beta_pv_plus	1,9	1.0
beta_pv_plus	2,9	1.0
beta_pv_plus	3,9	1.0
beta_pv_plus	4,9	1.0
beta_pv_plus	5,9	1.0
beta_pv_plus	1,10	1.0
beta_pv_plus	2,10	1.0
beta_pv_plus	3,10	1.0
beta_pv_plus	4,10	1.0
beta_pv_plus	5,10	1.0
beta_pv_plus	1,11	1.0
beta_pv_plus	2,11	1.0
beta_pv_plus	3,11	1.0
beta_pv_plus	4,11	1.0
beta_pv_plus	5,11	1.0
beta_pv_plus	1,12	1.0
beta_pv_plus	2,12	1.0
beta_pv_plus	3,12	1.0
beta_pv_plus	4,12	1.0
beta_pv_plus	5,12	1.0
beta_pv_plus	1,13	1.0
beta_pv_plus	2,13	1.0
beta_pv_plus	3,13	1.0
beta_pv_plus	4,13	1.0
beta_pv_plus	5,13	1.0
beta_pv_plus	1,14	1.0
beta_pv_plus	2,14	1.0
beta_pv_plus	3,14	1.0
beta_pv_plus	4,14	1.0
beta_pv_plus	5,14	1.0
beta_pv_plus	1,15	1.0
beta_pv_plus	2,15	1.0
beta_pv_plus	3,15	1.0
beta_pv_plus	4,15	1.0
beta_pv_plus	5,15	1.0
beta_pv_plus	1,16	1.0
beta_pv_plus	2,16	1.0
beta_pv_plus	3,16	1.0
beta_pv_plus	4,16	1.0
beta_pv_plus	5,16	1.0
beta_pv_plus	1,17	1.0
beta_pv_plus	2,17	1.0
beta_pv_plus	3,17	1.0
beta_pv_plus	4,17	1.0
beta_pv_plus	5,17	1.0
beta_pv_plus	1,18	1.0
beta_pv_plus	2,18	1.0
beta_pv_plus	3,18	1.0
beta_pv_plus	4,18	1.0
beta_pv_plus	5,18	1.0
beta_pv_plus	1,19	1.0
beta_pv_plus	2,19	1.0
beta_pv_plus	3,19	1.0
beta_pv_plus	4,19	1.0
beta_pv_plus	5,19	1.0
beta_pv_plus	1,20	1.0
beta_pv_plus	2,20	1.0
beta_pv_plus	3,20	1.0
beta_pv_plus	4,20	1.0
beta_pv_plus	5,20	1.0
beta_pv_plus	1,21	0.0
beta_pv_plus	2,21	0.0
beta_pv_plus	3,21	0.0
beta_pv_plus	4,21	0.0
beta_pv_plus	5,21	0.0
beta_pv_plus	1,22	0.0
beta_pv_plus	2,22	0.0
beta_pv_plus	3,22	0.0
beta_pv_plus	4,22	0.0
beta_pv_plus	5,22	0.0
beta_pv_plus	1,23	0.0
beta_pv_plus	2,23	0.0
beta_pv_plus	3,23	0.0
beta_pv_plus	4,23	0.0
beta_pv_plus	5,23	0.0
beta_pv_plus	1,24	0.0
beta_pv_plus	2,24	0.0
beta_pv_plus	3,24	0.0
beta_pv_plus	4,24	0.0
beta_pv_plus	5,24	0.0
beta_pv_plus	1,25	0.0
beta_pv_plus	2,25	0.0
beta_pv_plus	3,25	0.0
beta_pv_plus	4,25	0.0
beta_pv_plus	5,25	0.0
beta_pv_plus	1,26	0.0
beta_pv_plus	2,26	0.0
beta_pv_plus	3,26	0.0
beta_pv_plus	4,26	0.0
beta_pv_plus	5,26	0.0
beta_pv_plus	1,27	0.0
beta_pv_plus	2,27	0.0
beta_pv_plus	3,27	0.0
beta_pv_plus	4,27	0.0
beta_pv_plus	5,27	0.0
beta_pv_plus	1,28	0.0
beta_pv_plus	2,28	0.0
beta_pv_plus	3,28	0.0
beta_pv_plus	4,28	0.0
beta_pv_plus	5,28	0.0
beta_pv_plus	1,29	0.0
beta_pv_plus	2,29	0.0
beta_pv_plus	3,29	0.0
beta_pv_plus	4,29	0.0
beta_pv_plus	5,29	0.0
beta_pv_plus	1,30	0.0
beta_pv_plus	2,30	0.0
beta_pv_plus	3,30	0.0
beta_pv_plus	4,30	0.0
beta_pv_plus	5,30	0.0
beta_pv_plus	1,31	1.0
beta_pv_plus	2,31	1.0
beta_pv_plus	3,31	1.0
beta_pv_plus	4,31	1.0
beta_pv_plus	5,31	1.0
beta_pv_plus	1,32	1.0
beta_pv_plus	2,32	1.0
beta_pv_plus	3,32	1.0
beta_pv_plus	4,32	1.0
beta_pv_plus	5,32	1.0
beta_pv_plus	1,33	1.0
beta_pv_plus	2,33	1.0
beta_pv_plus	3,33	1.0
beta_pv_plus	4,33	1.0
beta_pv_plus	5,33	1.0
beta_pv_plus	1,34	1.0
beta_pv_plus	2,34	1.0
beta_pv_plus	3,34	1.0
beta_pv_plus	4,34	1.0
beta_pv_plus	5,34	1.0
beta_pv_plus	1,35	1.0
beta_pv_plus	2,35	1.0
beta_pv_plus	3,35	1.0
beta_pv_plus	4,35	1.0
beta_pv_plus	5,35	1.0
beta_pv_plus	1,36	1.0
beta_pv_plus	2,36	1.0
beta_pv_plus	3,36	1.0
beta_pv_plus	4,36	1.0
beta_pv_plus	5,36	1.0
beta_pv_plus	1,37	1.0
beta_pv_plus	2,37	1.0
beta_pv_plus	3,37	1.0
beta_pv_plus	4,37	1.0
beta_pv_plus	5,37	1.0
beta_pv_plus	1,38	1.0
beta_pv_plus	2,38	1.0
beta_pv_plus	3,38	1.0
beta_pv_plus	4,38	1.0
beta_pv_plus	5,38	1.0
beta_pv_plus	1,39	1.0
beta_pv_plus	2,39	1.0
beta_pv_plus	3,39	1.0
beta_pv_plus	4,39	1.0
beta_pv_plus	5,39	1.0
beta_pv_plus	1,40	1.0
beta_pv_plus	2,40	1.0
beta_pv_plus	3,40	1.0
beta_pv_plus	4,40	1.0
beta_pv_plus	5,40	1.0
beta_pv_plus	1,41	1.0
beta_pv_plus	2,41	1.0
beta_pv_plus	3,41	1.0
beta_pv_plus	4,41	1.0
beta_pv_plus	5,41	1.0
beta_pv_plus	1,42	1.0
beta_pv_plus	2,42	1.0
beta_pv_plus	3,42	1.0
beta_pv_plus	4,42	1.0
beta_pv_plus	5,42	1.0
beta_pv_plus	1,43	1.0
beta_pv_plus	2,43	1.0
beta_pv_plus	3,43	1.0
beta_pv_plus	4,43	1.0
beta_pv_plus	5,43	1.0
beta_pv_plus	1,44	1.0
beta_pv_plus	2,44	1.0
beta_pv_plus	3,44	1.0
beta_pv_plus	4,44	1.0
beta_pv_plus	5,44	1.0
beta_pv_plus	1,45	0.0
beta_pv_plus	2,45	0.0
beta_pv_plus	3,45	0.0
beta_pv_plus	4,45	0.0
beta_pv_plus	5,45	0.0
beta_pv_plus	1,46	0.0
beta_pv_plus	2,46	0.0
beta_pv_plus	3,46	0.0
beta_pv_plus	4,46	0.0
beta_pv_plus	5,46	0.0
beta_pv_plus	1,47	0.0
beta_pv_plus	2,47	0.0
beta_pv_plus	3,47	0.0
beta_pv_plus	4,47	0.0
beta_pv_plus	5,47	0.0
beta_pv_plus	1,48	0.0
beta_pv_plus	2,48	0.0
beta_pv_plus	3,48	0.0
beta_pv_plus	4,48	0.0
beta_pv_plus	5,48	0.0
beta_pv_plus	1,49	0.0
beta_pv_plus	2,49	0.0
beta_pv_plus	3,49	0.0
beta_pv_plus	4,49	0.0
beta_pv_plus	5,49	0.0
beta_pv_plus	1,50	0.0
beta_pv_plus	2,50	0.0
beta_pv_plus	3,50	0.0
beta_pv_plus	4,50	0.0
beta_pv_plus	5,50	0.0
beta_pv_plus	1,51	0.0
beta_pv_plus	2,51	0.0
beta_pv_plus	3,51	0.0
beta_pv_plus	4,51	0.0
beta_pv_plus	5,51	0.0
beta_pv_plus	1,52	0.0
beta_pv_plus	2,52	0.0
beta_pv_plus	3,52	0.0
beta_pv_plus	4,52	0.0
beta_pv_plus	5,52	0.0
beta_pv_plus	1,53	0.0
beta_pv_plus	2,53	0.0
beta_pv_plus	3,53	0.0
beta_pv_plus	4,53	0.0
beta_pv_plus	5,53	0.0
beta_pv_plus	1,54	0.0
beta_pv_plus	2,54	0.0
beta_pv_plus	3,54	0.0
beta_pv_plus	4,54	0.0
beta_pv_plus	5,54	0.0
beta_pv_plus	1,55	1.0
beta_pv_plus	2,55	1.0
beta_pv_plus	3,55	1.0
beta_pv_plus	4,55	1.0
beta_pv_plus	5,55	1.0
beta_pv_plus	1,56	1.0
beta_pv_plus	2,56	1.0
beta_pv_plus	3,56	1.0
beta_pv_plus	4,56	1.0
beta_pv_plus	5,56	1.0
beta_pv_plus	1,57	1.0
beta_pv_plus	2,57	1.0
beta_pv_plus	3,57	1.0
beta_pv_plus	4,57	1.0
beta_pv_plus	5,57	1.0
beta_pv_plus	1,58	1.0
beta_pv_plus	2,58	1.0
beta_pv_plus	3,58	1.0
beta_pv_plus	4,58	1.0
beta_pv_plus	5,58	1.0
beta_pv_plus	1,59	1.0
beta_pv_plus	2,59	1.0
beta_pv_plus	3,59	1.0
beta_pv_plus	4,59	1.0
beta_pv_plus	5,59	1.0
beta_pv_plus	1,60	1.0
beta_pv_plus	2,60	1.0
beta_pv_plus	3,60	1.0
beta_pv_plus	4,60	1.0
beta_pv_plus	5,60	1.0
beta_pv_plus	1,61	1.0
beta_pv_plus	2,61	1.0
beta_pv_plus	3,61	1.0
beta_pv_plus	4,61	1.0
beta_pv_plus	5,61	1.0
beta_pv_plus	1,62	1.0
beta_pv_plus	2,62	1.0
beta_pv_plus	3,62	1.0
beta_pv_plus	4,62	1.0
beta_pv_plus	5,62	1.0
beta_pv_plus	1,63	1.0
beta_pv_plus	2,63	1.0
beta_pv_plus	3,63	1.0
beta_pv_plus	4,63	1.0
beta_pv_plus	5,63	1.0
beta_pv_plus	1,64	1.0
beta_pv_plus	2,64	1.0
beta_pv_plus	3,64	1.0
beta_pv_plus	4,64	1.0
beta_pv_plus	5,64	1.0
beta_pv_plus	1,65	1.0
beta_pv_plus	2,65	1.0
beta_pv_plus	3,65	1.0
beta_pv_plus	4,65	1.0
beta_pv_plus	5,65	1.0
beta_pv_plus	1,66	1.0
beta_pv_plus	2,66	1.0
beta_pv_plus	3,66	1.0
beta_pv_plus	4,66	1.0
beta_pv_plus	5,66	1.0
beta_pv_plus	1,67	1.0
beta_pv_plus	2,67	1.0
beta_pv_plus	3,67	1.0
beta_pv_plus	4,67	1.0
beta_pv_plus	5,67	1.0
beta_pv_plus	1,68	1.0
beta_pv_plus	2,68	1.0
beta_pv_plus	3,68	1.0
beta_pv_plus	4,68	1.0
beta_pv_plus	5,68	1.0
beta_pv_plus	1,69	0.0
beta_pv_plus	2,69	0.0
beta_pv_plus	3,69	0.0
beta_pv_plus	4,69	0.0
beta_pv_plus	5,69	0.0
beta_pv_plus	1,70	0.0
beta_pv_plus	2,70	0.0
beta_pv_plus	3,70	0.0
beta_pv_plus	4,70	0.0
beta_pv_plus	5,70	0.0
beta_pv_plus	1,71	0.0
beta_pv_plus	2,71	0.0
beta_pv_plus	3,71	0.0
beta_pv_plus	4,71	0.0
beta_pv_plus	5,71	0.0
beta_pv_plus	1,72	0.0
beta_pv_plus	2,72	0.0
beta_pv_plus	3,72	0.0
beta_pv_plus	4,72	0.0
beta_pv_plus	5,72	0.0
beta_pv_plus	1,73	0.0
beta_pv_plus	2,73	0.0
beta_pv_plus	3,73	0.0
beta_pv_plus	4,73	0.0
beta_pv_plus	5,73	0.0
beta_pv_plus	1,74	0.0
beta_pv_plus	2,74	0.0
beta_pv_plus	3,74	0.0
beta_pv_plus	4,74	0.0
beta_pv_plus	5,74	0.0
beta_pv_plus	1,75	0.0
beta_pv_plus	2,75	0.0
beta_pv_plus	3,75	0.0
beta_pv_plus	4,75	0.0
beta_pv_plus	5,75	0.0
beta_pv_plus	1,76	0.0
beta_pv_plus	2,76	0.0
beta_pv_plus	3,76	0.0
beta_pv_plus	4,76	0.0
beta_pv_plus	5,76	0.0
beta_pv_plus	1,77	0.0
beta_pv_plus	2,77	0.0
beta_pv_plus	3,77	0.0
beta_pv_plus	4,77	0.0
beta_pv_plus	5,77	0.0
beta_pv_plus	1,78	0.0
beta_pv_plus	2,78	0.0
beta_pv_plus	3,78	0.0
beta_pv_plus	4,78	0.0
beta_pv_plus	5,78	0.0
beta_pv_plus	1,79	1.0
beta_pv_plus	2,79	1.0
beta_pv_plus	3,79	1.0
beta_pv_plus	4,79	1.0
beta_pv_plus	5,79	1.0
beta_pv_plus	1,80	1.0
beta_pv_plus	2,80	1.0
beta_pv_plus	3,80	1.0
beta_pv_plus	4,80	1.0
beta_pv_plus	5,80	1.0
beta_pv_plus	1,81	1.0
beta_pv_plus	2,81	1.0
beta_pv_plus	3,81	1.0
beta_pv_plus	4,81	1.0
beta_pv_plus	5,81	1.0
beta_pv_plus	1,82	1.0
beta_pv_plus	2,82	1.0
beta_pv_plus	3,82	1.0
beta_pv_plus	4,82	1.0
beta_pv_plus	5,82	1.0
beta_pv_plus	1,83	1.0
beta_pv_plus	2,83	1.0
beta_pv_plus	3,83	1.0
beta_pv_plus	4,83	1.0
beta_pv_plus	5,83	1.0
beta_pv_plus	1,84	1.0
beta_pv_plus	2,84	1.0
beta_pv_plus	3,84	1.0
beta_pv_plus	4,84	1.0
beta_pv_plus	5,84	1.0
beta_pv_plus	1,85	1.0
beta_pv_plus	2,85	1.0
beta_pv_plus	3,85	1.0
beta_pv_plus	4,85	1.0
beta_pv_plus	5,85	1.0
beta_pv_plus	1,86	1.0
beta_pv_plus	2,86	1.0
beta_pv_plus	3,86	1.0
beta_pv_plus	4,86	1.0
beta_pv_plus	5,86	1.0
beta_pv_plus	1,87	1.0
beta_pv_plus	2,87	1.0
beta_pv_plus	3,87	1.0
beta_pv_plus	4,87	1.0
beta_pv_plus	5,87	1.0
beta_pv_plus	1,88	1.0
beta_pv_plus	2,88	1.0
beta_pv_plus	3,88	1.0
beta_pv_plus	4,88	1.0
beta_pv_plus	5,88	1.0
beta_pv_plus	1,89	1.0
beta_pv_plus	2,89	1.0
beta_pv_plus	3,89	1.0
beta_pv_plus	4,89	1.0
beta_pv_plus	5,89	1.0
beta_pv_plus	1,90	1.0
beta_pv_plus	2,90	1.0
beta_pv_plus	3,90	1.0
beta_pv_plus	4,90	1.0
beta_pv_plus	5,90	1.0
beta_pv_plus	1,91	1.0
beta_pv_plus	2,91	1.0
beta_pv_plus	3,91	1.0
beta_pv_plus	4,91	1.0
beta_pv_plus	5,91	1.0
beta_pv_plus	1,92	1.0
beta_pv_plus	2,92	1.0
beta_pv_plus	3,92	1.0
beta_pv_plus	4,92	1.0
beta_pv_plus	5,92	1.0
beta_pv_plus	1,93	0.0
beta_pv_plus	2,93	0.0
beta_pv_plus	3,93	0.0
beta_pv_plus	4,93	0.0
beta_pv_plus	5,93	0.0
beta_pv_plus	1,94	0.0
beta_pv_plus	2,94	0.0
beta_pv_plus	3,94	0.0
beta_pv_plus	4,94	0.0
beta_pv_plus	5,94	0.0
beta_pv_plus	1,95	0.0
beta_pv_plus	2,95	0.0
beta_pv_plus	3,95	0.0
beta_pv_plus	4,95	0.0
beta_pv_plus	5,95	0.0
beta_pv_plus	1,96	0.0
beta_pv_plus	2,96	0.0
beta_pv_plus	3,96	0.0
beta_pv_plus	4,96	0.0
beta_pv_plus	5,96	0.0
beta_wt_minus	1,1	-0.0
beta_wt_minus	2,1	-0.0
beta_wt_minus	3,1	-0.0
beta_wt_minus	4,1	-0.0
beta_wt_minus	5,1	-0.0
beta_wt_minus	1,2	-0.0
beta_wt_minus	2,2	-0.0
beta_wt_minus	3,2	-0.0
beta_wt_minus	4,2	-0.0
beta_wt_minus	5,2	-0.0
beta_wt_minus	1,3	-0.0
beta_wt_minus	2,3	-0.0
beta_wt_minus	3,3	-0.0
beta_wt_minus	4,3	-0.0
beta_wt_minus	5,3	-0.0
beta_wt_minus	1,4	-0.0
beta_wt_minus	2,4	-0.0
beta_wt_minus	3,4	-0.0
beta_wt_minus	4,4	-0.0
beta_wt_minus	5,4	-0.0
beta_wt_minus	1,5	-0.0
beta_wt_minus	2,5	-0.0
beta_wt_minus	3,5	-0.0
beta_wt_minus	4,5	-0.0
beta_wt_minus	5,5	-0.0
beta_wt_minus	1,6	-0.0
beta_wt_minus	2,6	-0.0
beta_wt_minus	3,6	-0.0
beta_wt_minus	4,6	-0.0
beta_wt_minus	5,6	-0.0
beta_wt_minus	1,7	-0.0
beta_wt_minus	2,7	-0.0
beta_wt_minus	3,7	-0.0
beta_wt_minus	4,7	-0.0
beta_wt_minus	5,7	-0.0
beta_wt_minus	1,8	-0.0
beta_wt_minus	2,8	-0.0
beta_wt_minus	3,8	-0.0
beta_wt_minus	4,8	-0.0
beta_wt_minus	5,8	-0.0
beta_wt_minus	1,9	-0.0
beta_wt_minus	2,9	-0.0
beta_wt_minus	3,9	-0.0
beta_wt_minus	4,9	-0.0
beta_wt_minus	5,9	-0.0
beta_wt_minus	1,10	-0.0
beta_wt_minus	2,10	-0.0
beta_wt_minus	3,10	-0.0
beta_wt_minus	4,10	-0.0
beta_wt_minus	5,10	-0.0
beta_wt_minus	1,11	-0.0
beta_wt_minus	2,11	-0.0
beta_wt_minus	3,11	-0.0
beta_wt_minus	4,11	-0.0
beta_wt_minus	5,11	-0.0
beta_wt_minus	1,12	-0.0
beta_wt_minus	2,12	-0.0
beta_wt_minus	3,12	-0.0
beta_wt_minus	4,12	-0.0
beta_wt_minus	5,12	-0.0
beta_wt_minus	1,13	-0.0
beta_wt_minus	2,13	-0.0
beta_wt_minus	3,13	-0.0
beta_wt_minus	4,13	-0.0
beta_wt_minus	5,13	-0.0
beta_wt_minus	1,14	-0.0
beta_wt_minus	2,14	-0.0
beta_wt_minus	3,14	-0.0
beta_wt_minus	4,14	-0.0
beta_wt_minus	5,14	-0.0
beta_wt_minus	1,15	-0.0
beta_wt_minus	2,15	-0.0
beta_wt_minus	3,15	-0.0
beta_wt_minus	4,15	-0.0
beta_wt_minus	5,15	-0.0
beta_wt_minus	1,16	-0.0
beta_wt_minus	2,16	-0.0
beta_wt_minus	3,16	-0.0
beta_wt_minus	4,16	-0.0
beta_wt_minus	5,16	-0.0
beta_wt_minus	1,17	-0.0
beta_wt_minus	2,17	-0.0
beta_wt_minus	3,17	-0.0
beta_wt_minus	4,17	-0.0
beta_wt_minus	5,17	-0.0
beta_wt_minus	1,18	-0.0
beta_wt_minus	2,18	-0.0
beta_wt_minus	3,18	-0.0
beta_wt_minus	4,18	-0.0
beta_wt_minus	5,18	-0.0
beta_wt_minus	1,19	-0.0
beta_wt_minus	2,19	-0.0
beta_wt_minus	3,19	-0.0
beta_wt_minus	4,19	-0.0
beta_wt_minus	5,19	-0.0
beta_wt_minus	1,20	-0.0
beta_wt_minus	2,20	-0.0
beta_wt_minus	3,20	-0.0
beta_wt_minus	4,20	-0.0
beta_wt_minus	5,20	-0.0
beta_wt_minus	1,21	-0.0
beta_wt_minus	2,21	-0.0
beta_wt_minus	3,21	-0.0
beta_wt_minus	4,21	-0.0
beta_wt_minus	5,21	-0.0
beta_wt_minus	1,22	-0.0
beta_wt_minus	2,22	-0.0
beta_wt_minus	3,22	-0.0
beta_wt_minus	4,22	-0.0
beta_wt_minus	5,22	-0.0
beta_wt_minus	1,23	-0.0
beta_wt_minus	2,23	-0.0
beta_wt_minus	3,23	-0.0
beta_wt_minus	4,23	-0.0
beta_wt_minus	5,23	-0.0
beta_wt_minus	1,24	-0.0
beta_wt_minus	2,24	-0.0
beta_wt_minus	3,24	-0.0
beta_wt_minus	4,24	-0.0
beta_wt_minus	5,24	-0.0
beta_wt_minus	1,25	-0.0
beta_wt_minus	2,25	-0.0
beta_wt_minus	3,25	-0.0
beta_wt_minus	4,25	-0.0
beta_wt_minus	5,25	-0.0
beta_wt_minus	1,26	-0.0
beta_wt_minus	2,26	-0.0
beta_wt_minus	3,26	-0.0
beta_wt_minus	4,26	-0.0
beta_wt_minus	5,26	-0.0
beta_wt_minus	1,27	-0.0
beta_wt_minus	2,27	-0.0
beta_wt_minus	3,27	-0.0
beta_wt_minus	4,27	-0.0
beta_wt_minus	5,27	-0.0
beta_wt_minus	1,28	-0.0
beta_wt_minus	2,28	-0.0
beta_wt_minus	3,28	-0.0
beta_wt_minus	4,28	-0.0
beta_wt_minus	5,28	-0.0
beta_wt_minus	1,29	-0.0
beta_wt_minus	2,29	-0.0
beta_wt_minus	3,29	-0.0
beta_wt_minus	4,29	-0.0
beta_wt_minus	5,29	-0.0
beta_wt_minus	1,30	-0.0
beta_wt_minus	2,30	-0.0
beta_wt_minus	3,30	-0.0
beta_wt_minus	4,30	-0.0
beta_wt_minus	5,30	-0.0
beta_wt_minus	1,31	-0.0
beta_wt_minus	2,31	-0.0
beta_wt_minus	3,31	-0.0
beta_wt_minus	4,31	-0.0
beta_wt_minus	5,31	-0.0
beta_wt_minus	1,32	-0.0
beta_wt_minus	2,32	-0.0
beta_wt_minus	3,32	-0.0
beta_wt_minus	4,32	-0.0
beta_wt_minus	5,32	-0.0
beta_wt_minus	1,33	-0.0
beta_wt_minus	2,33	-0.0
beta_wt_minus	3,33	-0.0
beta_wt_minus	4,33	-0.0
beta_wt_minus	5,33	-0.0
beta_wt_minus	1,34	-0.0
beta_wt_minus	2,34	-0.0
beta_wt_minus	3,34	-0.0
beta_wt_minus	4,34	-0.0
beta_wt_minus	5,34	-0.0
beta_wt_minus	1,35	-0.0
beta_wt_minus	2,35	-0.0
beta_wt_minus	3,35	-0.0
beta_wt_minus	4,35	-0.0
beta_wt_minus	5,35	-0.0
beta_wt_minus	1,36	-0.0
beta_wt_minus	2,36	-0.0
beta_wt_minus	3,36	-0.0
beta_wt_minus	4,36	-0.0
beta_wt_minus	5,36	-0.0
beta_wt_minus	1,37	-0.0
beta_wt_minus	2,37	-0.0
beta_wt_minus	3,37	-0.0
beta_wt_minus	4,37	-0.0
beta_wt_minus	5,37	-0.0
beta_wt_minus	1,38	-0.0
beta_wt_minus	2,38	-0.0
beta_wt_minus	3,38	-0.0
beta_wt_minus	4,38	-0.0
beta_wt_minus	5,38	-0.0
beta_wt_minus	1,39	-0.0
beta_wt_minus	2,39	-0.0
beta_wt_minus	3,39	-0.0
beta_wt_minus	4,39	-0.0
beta_wt_minus	5,39	-0.0
beta_wt_minus	1,40	-0.0
beta_wt_minus	2,40	-0.0
beta_wt_minus	3,40	-0.0
beta_wt_minus	4,40	-0.0
beta_wt_minus	5,40	-0.0
beta_wt_minus	1,41	-0.0
beta_wt_minus	2,41	-0.0
beta_wt_minus	3,41	-0.0
beta_wt_minus	4,41	-0.0
beta_wt_minus	5,41	-0.0
beta_wt_minus	1,42	-0.0
beta_wt_minus	2,42	-0.0
beta_wt_minus	3,42	-0.0
beta_wt_minus	4,42	-0.0
beta_wt_minus	5,42	-0.0
beta_wt_minus	1,43	-0.0
beta_wt_minus	2,43	-0.0
beta_wt_minus	3,43	-0.0
beta_wt_minus	4,43	-0.0
beta_wt_minus	5,43	-0.0
beta_wt_minus	1,44	-0.0
beta_wt_minus	2,44	-0.0
beta_wt_minus	3,44	-0.0
beta_wt_minus	4,44	-0.0
beta_wt_minus	5,44	-0.0
beta_wt_minus	1,45	-0.0
beta_wt_minus	2,45	-0.0
beta_wt_minus	3,45	-0.0
beta_wt_minus	4,45	-0.0
beta_wt_minus	5,45	-0.0
beta_wt_minus	1,46	-0.0
beta_wt_minus	2,46	-0.0
beta_wt_minus	3,46	-0.0
beta_wt_minus	4,46	-0.0
beta_wt_minus	5,46	-0.0
beta_wt_minus	1,47	-0.0
beta_wt_minus	2,47	-0.0
beta_wt_minus	3,47	-0.0
beta_wt_minus	4,47	-0.0
beta_wt_minus	5,47	-0.0
beta_wt_minus	1,48	-0.0
beta_wt_minus	2,48	-0.0
beta_wt_minus	3,48	-0.0
beta_wt_minus	4,48	-0.0
beta_wt_minus	5,48	-0.0
beta_wt_minus	1,49	-0.0
beta_wt_minus	2,49	-0.0
beta_wt_minus	3,49	-0.0
beta_wt_minus	4,49	-0.0
beta_wt_minus	5,49	-0.0
beta_wt_minus	1,50	-0.0
beta_wt_minus	2,50	-0.0
beta_wt_minus	3,50	-0.0
beta_wt_minus	4,50	-0.0
beta_wt_minus	5,50	-0.0
beta_wt_minus	1,51	-0.0
beta_wt_minus	2,51	-0.0
beta_wt_minus	3,51	-0.0
beta_wt_minus	4,51	-0.0
beta_wt_minus	5,51	-0.0
beta_wt_minus	1,52	-0.0
beta_wt_minus	2,52	-0.0
beta_wt_minus	3,52	-0.0
beta_wt_minus	4,52	-0.0
beta_wt_minus	5,52	-0.0
beta_wt_minus	1,53	-0.0
beta_wt_minus	2,53	-0.0
beta_wt_minus	3,53	-0.0
beta_wt_minus	4,53	-0.0
beta_wt_minus	5,53	-0.0
beta_wt_minus	1,54	-0.0
beta_wt_minus	2,54	-0.0
beta_wt_minus	3,54	-0.0
beta_wt_minus	4,54	-0.0
beta_wt_minus	5,54	-0.0
beta_wt_minus	1,55	-0.0
beta_wt_minus	2,55	-0.0
beta_wt_minus	3,55	-0.0
beta_wt_minus	4,55	-0.0
beta_wt_minus	5,55	-0.0
beta_wt_minus	1,56	-0.0
beta_wt_minus	2,56	-0.0
beta_wt_minus	3,56	-0.0
beta_wt_minus	4,56	-0.0
beta_wt_minus	5,56	-0.0
beta_wt_minus	1,57	-0.0
beta_wt_minus	2,57	-0.0
beta_wt_minus	3,57	-0.0
beta_wt_minus	4,57	-0.0
beta_wt_minus	5,57	-0.0
beta_wt_minus	1,58	-0.0
beta_wt_minus	2,58	-0.0
beta_wt_minus	3,58	-0.0
beta_wt_minus	4,58	-0.0
beta_wt_minus	5,58	-0.0
beta_wt_minus	1,59	-0.0
beta_wt_minus	2,59	-0.0
beta_wt_minus	3,59	-0.0
beta_wt_minus	4,59	-0.0
beta_wt_minus	5,59	-0.0
beta_wt_minus	1,60	-0.0
beta_wt_minus	2,60	-0.0
beta_wt_minus	3,60	-0.0
beta_wt_minus	4,60	-0.0
beta_wt_minus	5,60	-0.0
beta_wt_minus	1,61	-0.0
beta_wt_minus	2,61	-0.0
beta_wt_minus	3,61	-0.0
beta_wt_minus	4,61	-0.0
beta_wt_minus	5,61	-0.0
beta_wt_minus	1,62	-0.0
beta_wt_minus	2,62	-0.0
beta_wt_minus	3,62	-0.0
beta_wt_minus	4,62	-0.0
beta_wt_minus	5,62	-0.0
beta_wt_minus	1,63	-0.0
beta_wt_minus	2,63	-0.0
beta_wt_minus	3,63	-0.0
beta_wt_minus	4,63	-0.0
beta_wt_minus	5,63	-0.0
beta_wt_minus	1,64	-0.0
beta_wt_minus	2,64	-0.0
beta_wt_minus	3,64	-0.0
beta_wt_minus	4,64	-0.0
beta_wt_minus	5,64	-0.0
beta_wt_minus	1,65	-0.0
beta_wt_minus	2,65	-0.0
beta_wt_minus	3,65	-0.0
beta_wt_minus	4,65	-0.0
beta_wt_minus	5,65	-0.0
beta_wt_minus	1,66	-0.0
beta_wt_minus	2,66	-0.0
beta_wt_minus	3,66	-0.0
beta_wt_minus	4,66	-0.0
beta_wt_minus	5,66	-0.0
beta_wt_minus	1,67	-0.0
beta_wt_minus	2,67	-0.0
beta_wt_minus	3,67	-0.0
beta_wt_minus	4,67	-0.0
beta_wt_minus	5,67	-0.0
beta_wt_minus	1,68	-0.0
beta_wt_minus	2,68	-0.0
beta_wt_minus	3,68	-0.0
beta_wt_minus	4,68	-0.0
beta_wt_minus	5,68	-0.0
beta_wt_minus	1,69	-0.0
beta_wt_minus	2,69	-0.0
beta_wt_minus	3,69	-0.0
beta_wt_minus	4,69	-0.0
beta_wt_minus	5,69	-0.0
beta_wt_minus	1,70	-0.0
beta_wt_minus	2,70	-0.0
beta_wt_minus	3,70	-0.0
beta_wt_minus	4,70	-0.0
beta_wt_minus	5,70	-0.0
beta_wt_minus	1,71	-0.0
beta_wt_minus	2,71	-0.0
beta_wt_minus	3,71	-0.0
beta_wt_minus	4,71	-0.0
beta_wt_minus	5,71	-0.0
beta_wt_minus	1,72	-0.0
beta_wt_minus	2,72	-0.0
beta_wt_minus	3,72	-0.0
beta_wt_minus	4,72	-0.0
beta_wt_minus	5,72	-0.0
beta_wt_minus	1,73	-0.0
beta_wt_minus	2,73	-0.0
beta_wt_minus	3,73	-0.0
beta_wt_minus	4,73	-0.0
beta_wt_minus	5,73	-0.0
beta_wt_minus	1,74	-0.0
beta_wt_minus	2,74	-0.0
beta_wt_minus	3,74	-0.0
beta_wt_minus	4,74	-0.0
beta_wt_minus	5,74	-0.0
beta_wt_minus	1,75	-0.0
beta_wt_minus	2,75	-0.0
beta_wt_minus	3,75	-0.0
beta_wt_minus	4,75	-0.0
beta_wt_minus	5,75	-0.0
beta_wt_minus	1,76	-0.0
beta_wt_minus	2,76	-0.0
beta_wt_minus	3,76	-0.0
beta_wt_minus	4,76	-0.0
beta_wt_minus	5,76	-0.0
beta_wt_minus	1,77	-0.0
beta_wt_minus	2,77	-0.0
beta_wt_minus	3,77	-0.0
beta_wt_minus	4,77	-0.0
beta_wt_minus	5,77	-0.0
beta_wt_minus	1,78	-0.0
beta_wt_minus	2,78	-0.0
beta_wt_minus	3,78	-0.0
beta_wt_minus	4,78	-0.0
beta_wt_minus	5,78	-0.0
beta_wt_minus	1,79	-0.0
beta_wt_minus	2,79	-0.0
beta_wt_minus	3,79	-0.0
beta_wt_minus	4,79	-0.0
beta_wt_minus	5,79	-0.0
beta_wt_minus	1,80	-0.0
beta_wt_minus	2,80	-0.0
beta_wt_minus	3,80	-0.0
beta_wt_minus	4,80	-0.0
beta_wt_minus	5,80	-0.0
beta_wt_minus	1,81	-0.0
beta_wt_minus	2,81	-0.0
beta_wt_minus	3,81	-0.0
beta_wt_minus	4,81	-0.0
beta_wt_minus	5,81	-0.0
beta_wt_minus	1,82	-0.0
beta_wt_minus	2,82	-0.0
beta_wt_minus	3,82	-0.0
beta_wt_minus	4,82	-0.0
beta_wt_minus	5,82	-0.0
beta_wt_minus	1,83	-0.0
beta_wt_minus	2,83	-0.0
beta_wt_minus	3,83	-0.0
beta_wt_minus	4,83	-0.0
beta_wt_minus	5,83	-0.0
beta_wt_minus	1,84	-0.0
beta_wt_minus	2,84	-0.0
beta_wt_minus	3,84	-0.0
beta_wt_minus	4,84	-0.0
beta_wt_minus	5,84	-0.0
beta_wt_minus	1,85	-0.0
beta_wt_minus	2,85	-0.0
beta_wt_minus	3,85	-0.0
beta_wt_minus	4,85	-0.0
beta_wt_minus	5,85	-0.0
beta_wt_minus	1,86	-0.0
beta_wt_minus	2,86	-0.0
beta_wt_minus	3,86	-0.0
beta_wt_minus	4,86	-0.0
beta_wt_minus	5,86	-0.0
beta_wt_minus	1,87	-0.0
beta_wt_minus	2,87	-0.0
beta_wt_minus	3,87	-0.0
beta_wt_minus	4,87	-0.0
beta_wt_minus	5,87	-0.0
beta_wt_minus	1,88	-0.0
beta_wt_minus	2,88	-0.0
beta_wt_minus	3,88	-0.0
beta_wt_minus	4,88	-0.0
beta_wt_minus	5,88	-0.0
beta_wt_minus	1,89	-0.0
beta_wt_minus	2,89	-0.0
beta_wt_minus	3,89	-0.0
beta_wt_minus	4,89	-0.0
beta_wt_minus	5,89	-0.0
beta_wt_minus	1,90	-0.0
beta_wt_minus	2,90	-0.0
beta_wt_minus	3,90	-0.0
beta_wt_minus	4,90	-0.0
beta_wt_minus	5,90	-0.0
beta_wt_minus	1,91	-0.0
beta_wt_minus	2,91	-0.0
beta_wt_minus	3,91	-0.0
beta_wt_minus	4,91	-0.0
beta_wt_minus	5,91	-0.0
beta_wt_minus	1,92	-0.0
beta_wt_minus	2,92	-0.0
beta_wt_minus	3,92	-0.0
beta_wt_minus	4,92	-0.0
beta_wt_minus	5,92	-0.0
beta_wt_minus	1,93	-0.0
beta_wt_minus	2,93	-0.0
beta_wt_minus	3,93	-0.0
beta_wt_minus	4,93	-0.0
beta_wt_minus	5,93	-0.0
beta_wt_minus	1,94	-0.0
beta_wt_minus	2,94	-0.0
beta_wt_minus	3,94	-0.0
beta_wt_minus	4,94	-0.0
beta_wt_minus	5,94	-0.0
beta_wt_minus	1,95	-0.0
beta_wt_minus	2,95	-0.0
beta_wt_minus	3,95	-0.0
beta_wt_minus	4,95	-0.0
beta_wt_minus	5,95	-0.0
beta_wt_minus	1,96	-0.0
beta_wt_minus	2,96	-0.0
beta_wt_minus	3,96	-0.0
beta_wt_minus	4,96	-0.0
beta_wt_minus	5,96	-0.0
beta_wt_plus	1,1	1.0
beta_wt_plus	2,1	1.0
beta_wt_plus	3,1	1.0
beta_wt_plus	4,1	1.0
beta_wt_plus	5,1	1.0
beta_wt_plus	1,2	1.0
beta_wt_plus	2,2	1.0
beta_wt_plus	3,2	1.0
beta_wt_plus	4,2	1.0
beta_wt_plus	5,2	1.0
beta_wt_plus	1,3	1.0
beta_wt_plus	2,3	1.0
beta_wt_plus	3,3	1.0
beta_wt_plus	4,3	1.0
beta_wt_plus	5,3	1.0
beta_wt_plus	1,4	1.0
beta_wt_plus	2,4	1.0
beta_wt_plus	3,4	1.0
beta_wt_plus	4,4	1.0
beta_wt_plus	5,4	1.0
beta_wt_plus	1,5	1.0
beta_wt_plus	2,5	1.0
beta_wt_plus	3,5	1.0
beta_wt_plus	4,5	1.0
beta_wt_plus	5,5	1.0
beta_wt_plus	1,6	1.0
beta_wt_plus	2,6	1.0
beta_wt_plus	3,6	1.0
beta_wt_plus	4,6	1.0
beta_wt_plus	5,6	1.0
beta_wt_plus	1,7	1.0
beta_wt_plus	2,7	1.0
beta_wt_plus	3,7	1.0
beta_wt_plus	4,7	1.0
beta_wt_plus	5,7	1.0
beta_wt_plus	1,8	1.0
beta_wt_plus	2,8	1.0
beta_wt_plus	3,8	1.0
beta_wt_plus	4,8	1.0
beta_wt_plus	5,8	1.0
beta_wt_plus	1,9	1.0
beta_wt_plus	2,9	1.0
beta_wt_plus	3,9	1.0
beta_wt_plus	4,9	1.0
beta_wt_plus	5,9	1.0
beta_wt_plus	1,10	1.0
beta_wt_plus	2,10	1.0
beta_wt_plus	3,10	1.0
beta_wt_plus	4,10	1.0
beta_wt_plus	5,10	1.0
beta_wt_plus	1,11	1.0
beta_wt_plus	2,11	1.0
beta_wt_plus	3,11	1.0
beta_wt_plus	4,11	1.0
beta_wt_plus	5,11	1.0
beta_wt_plus	1,12	1.0
beta_wt_plus	2,12	1.0
beta_wt_plus	3,12	1.0
beta_wt_plus	4,12	1.0
beta_wt_plus	5,12	1.0
beta_wt_plus	1,13	1.0
beta_wt_plus	2,13	1.0
beta_wt_plus	3,13	1.0
beta_wt_plus	4,13	1.0
beta_wt_plus	5,13	1.0
beta_wt_plus	1,14	1.0
beta_wt_plus	2,14	1.0
beta_wt_plus	3,14	1.0
beta_wt_plus	4,14	1.0
beta_wt_plus	5,14	1.0
beta_wt_plus	1,15	1.0
beta_wt_plus	2,15	1.0
beta_wt_plus	3,15	1.0
beta_wt_plus	4,15	1.0
beta_wt_plus	5,15	1.0
beta_wt_plus	1,16	1.0
beta_wt_plus	2,16	1.0
beta_wt_plus	3,16	1.0
beta_wt_plus	4,16	1.0
beta_wt_plus	5,16	1.0
beta_wt_plus	1,17	1.0
beta_wt_plus	2,17	1.0
beta_wt_plus	3,17	1.0
beta_wt_plus	4,17	1.0
beta_wt_plus	5,17	1.0
beta_wt_plus	1,18	1.0
beta_wt_plus	2,18	1.0
beta_wt_plus	3,18	1.0
beta_wt_plus	4,18	1.0
beta_wt_plus	5,18	1.0
beta_wt_plus	1,19	1.0
beta_wt_plus	2,19	1.0
beta_wt_plus	3,19	1.0
beta_wt_plus	4,19	1.0
beta_wt_plus	5,19	1.0
beta_wt_plus	1,20	1.0
beta_wt_plus	2,20	1.0
beta_wt_plus	3,20	1.0
beta_wt_plus	4,20	1.0
beta_wt_plus	5,20	1.0
beta_wt_plus	1,21	1.0
beta_wt_plus	2,21	1.0
beta_wt_plus	3,21	1.0
beta_wt_plus	4,21	1.0
beta_wt_plus	5,21	1.0
beta_wt_plus	1,22	1.0
beta_wt_plus	2,22	1.0
beta_wt_plus	3,22	1.0
beta_wt_plus	4,22	1.0
beta_wt_plus	5,22	1.0
beta_wt_plus	1,23	1.0
beta_wt_plus	2,23	1.0
beta_wt_plus	3,23	1.0
beta_wt_plus	4,23	1.0
beta_wt_plus	5,23	1.0
beta_wt_plus	1,24	1.0
beta_wt_plus	2,24	1.0
beta_wt_plus	3,24	1.0
beta_wt_plus	4,24	1.0
beta_wt_plus	5,24	1.0
beta_wt_plus	1,25	1.0
beta_wt_plus	2,25	1.0
beta_wt_plus	3,25	1.0
beta_wt_plus	4,25	1.0
beta_wt_plus	5,25	1.0
beta_wt_plus	1,26	1.0
beta_wt_plus	2,26	1.0
beta_wt_plus	3,26	1.0
beta_wt_plus	4,26	1.0
beta_wt_plus	5,26	1.0
beta_wt_plus	1,27	1.0
beta_wt_plus	2,27	1.0
beta_wt_plus	3,27	1.0
beta_wt_plus	4,27	1.0
beta_wt_plus	5,27	1.0
beta_wt_plus	1,28	1.0
beta_wt_plus	2,28	1.0
beta_wt_plus	3,28	1.0
beta_wt_plus	4,28	1.0
beta_wt_plus	5,28	1.0
beta_wt_plus	1,29	1.0
beta_wt_plus	2,29	1.0
beta_wt_plus	3,29	1.0
beta_wt_plus	4,29	1.0
beta_wt_plus	5,29	1.0
beta_wt_plus	1,30	1.0
beta_wt_plus	2,30	1.0
beta_wt_plus	3,30	1.0
beta_wt_plus	4,30	1.0
beta_wt_plus	5,30	1.0
beta_wt_plus	1,31	1.0
beta_wt_plus	2,31	1.0
beta_wt_plus	3,31	1.0
beta_wt_plus	4,31	1.0
beta_wt_plus	5,31	1.0
beta_wt_plus	1,32	1.0
beta_wt_plus	2,32	1.0
beta_wt_plus	3,32	1.0
beta_wt_plus	4,32	1.0
beta_wt_plus	5,32	1.0
beta_wt_plus	1,33	1.0
beta_wt_plus	2,33	1.0
beta_wt_plus	3,33	1.0
beta_wt_plus	4,33	1.0
beta_wt_plus	5,33	1.0
beta_wt_plus	1,34	1.0
beta_wt_plus	2,34	1.0
beta_wt_plus	3,34	1.0
beta_wt_plus	4,34	1.0
beta_wt_plus	5,34	1.0
beta_wt_plus	1,35	1.0
beta_wt_plus	2,35	1.0
beta_wt_plus	3,35	1.0
beta_wt_plus	4,35	1.0
beta_wt_plus	5,35	1.0
beta_wt_plus	1,36	1.0
beta_wt_plus	2,36	1.0
beta_wt_plus	3,36	1.0
beta_wt_plus	4,36	1.0
beta_wt_plus	5,36	1.0
beta_wt_plus	1,37	1.0
beta_wt_plus	2,37	1.0
beta_wt_plus	3,37	1.0
beta_wt_plus	4,37	1.0
beta_wt_plus	5,37	1.0
beta_wt_plus	1,38	1.0
beta_wt_plus	2,38	1.0
beta_wt_plus	3,38	1.0
beta_wt_plus	4,38	1.0
beta_wt_plus	5,38	1.0
beta_wt_plus	1,39	1.0
beta_wt_plus	2,39	1.0
beta_wt_plus	3,39	1.0
beta_wt_plus	4,39	1.0
beta_wt_plus	5,39	1.0
beta_wt_plus	1,40	1.0
beta_wt_plus	2,40	1.0
beta_wt_plus	3,40	1.0
beta_wt_plus	4,40	1.0
beta_wt_plus	5,40	1.0
beta_wt_plus	1,41	1.0
beta_wt_plus	2,41	1.0
beta_wt_plus	3,41	1.0
beta_wt_plus	4,41	1.0
beta_wt_plus	5,41	1.0
beta_wt_plus	1,42	1.0
beta_wt_plus	2,42	1.0
beta_wt_plus	3,42	1.0
beta_wt_plus	4,42	1.0
beta_wt_plus	5,42	1.0
beta_wt_plus	1,43	1.0
beta_wt_plus	2,43	1.0
beta_wt_plus	3,43	1.0
beta_wt_plus	4,43	1.0
beta_wt_plus	5,43	1.0
beta_wt_plus	1,44	1.0
beta_wt_plus	2,44	1.0
beta_wt_plus	3,44	1.0
beta_wt_plus	4,44	1.0
beta_wt_plus	5,44	1.0
beta_wt_plus	1,45	1.0
beta_wt_plus	2,45	1.0
beta_wt_plus	3,45	1.0
beta_wt_plus	4,45	1.0
beta_wt_plus	5,45	1.0
beta_wt_plus	1,46	1.0
beta_wt_plus	2,46	1.0
beta_wt_plus	3,46	1.0
beta_wt_plus	4,46	1.0
beta_wt_plus	5,46	1.0
beta_wt_plus	1,47	1.0
beta_wt_plus	2,47	1.0
beta_wt_plus	3,47	1.0
beta_wt_plus	4,47	1.0
beta_wt_plus	5,47	1.0
beta_wt_plus	1,48	1.0
beta_wt_plus	2,48	1.0
beta_wt_plus	3,48	1.0
beta_wt_plus	4,48	1.0
beta_wt_plus	5,48	1.0
beta_wt_plus	1,49	1.0
beta_wt_plus	2,49	1.0
beta_wt_plus	3,49	1.0
beta_wt_plus	4,49	1.0
beta_wt_plus	5,49	1.0
beta_wt_plus	1,50	1.0
beta_wt_plus	2,50	1.0
beta_wt_plus	3,50	1.0
beta_wt_plus	4,50	1.0
beta_wt_plus	5,50	1.0
beta_wt_plus	1,51	1.0
beta_wt_plus	2,51	1.0
beta_wt_plus	3,51	1.0
beta_wt_plus	4,51	1.0
beta_wt_plus	5,51	1.0
beta_wt_plus	1,52	1.0
beta_wt_plus	2,52	1.0
beta_wt_plus	3,52	1.0
beta_wt_plus	4,52	1.0
beta_wt_plus	5,52	1.0
beta_wt_plus	1,53	1.0
beta_wt_plus	2,53	1.0
beta_wt_plus	3,53	1.0
beta_wt_plus	4,53	1.0
beta_wt_plus	5,53	1.0
beta_wt_plus	1,54	1.0
beta_wt_plus	2,54	1.0
beta_wt_plus	3,54	1.0
beta_wt_plus	4,54	1.0
beta_wt_plus	5,54	1.0
beta_wt_plus	1,55	1.0
beta_wt_plus	2,55	1.0
beta_wt_plus	3,55	1.0
beta_wt_plus	4,55	1.0
beta_wt_plus	5,55	1.0
beta_wt_plus	1,56	1.0
beta_wt_plus	2,56	1.0
beta_wt_plus	3,56	1.0
beta_wt_plus	4,56	1.0
beta_wt_plus	5,56	1.0
beta_wt_plus	1,57	1.0
beta_wt_plus	2,57	1.0
beta_wt_plus	3,57	1.0
beta_wt_plus	4,57	1.0
beta_wt_plus	5,57	1.0
beta_wt_plus	1,58	1.0
beta_wt_plus	2,58	1.0
beta_wt_plus	3,58	1.0
beta_wt_plus	4,58	1.0
beta_wt_plus	5,58	1.0
beta_wt_plus	1,59	1.0
beta_wt_plus	2,59	1.0
beta_wt_plus	3,59	1.0
beta_wt_plus	4,59	1.0
beta_wt_plus	5,59	1.0
beta_wt_plus	1,60	1.0
beta_wt_plus	2,60	1.0
beta_wt_plus	3,60	1.0
beta_wt_plus	4,60	1.0
beta_wt_plus	5,60	1.0
beta_wt_plus	1,61	1.0
beta_wt_plus	2,61	1.0
beta_wt_plus	3,61	1.0
beta_wt_plus	4,61	1.0
beta_wt_plus	5,61	1.0
beta_wt_plus	1,62	1.0
beta_wt_plus	2,62	1.0
beta_wt_plus	3,62	1.0
beta_wt_plus	4,62	1.0
beta_wt_plus	5,62	1.0
beta_wt_plus	1,63	1.0
beta_wt_plus	2,63	1.0
beta_wt_plus	3,63	1.0
beta_wt_plus	4,63	1.0
beta_wt_plus	5,63	1.0
beta_wt_plus	1,64	1.0
beta_wt_plus	2,64	1.0
beta_wt_plus	3,64	1.0
beta_wt_plus	4,64	1.0
beta_wt_plus	5,64	1.0
beta_wt_plus	1,65	1.0
beta_wt_plus	2,65	1.0
beta_wt_plus	3,65	1.0
beta_wt_plus	4,65	1.0
beta_wt_plus	5,65	1.0
beta_wt_plus	1,66	1.0
beta_wt_plus	2,66	1.0
beta_wt_plus	3,66	1.0
beta_wt_plus	4,66	1.0
beta_wt_plus	5,66	1.0
beta_wt_plus	1,67	1.0
beta_wt_plus	2,67	1.0
beta_wt_plus	3,67	1.0
beta_wt_plus	4,67	1.0
beta_wt_plus	5,67	1.0
beta_wt_plus	1,68	1.0
beta_wt_plus	2,68	1.0
beta_wt_plus	3,68	1.0
beta_wt_plus	4,68	1.0
beta_wt_plus	5,68	1.0
beta_wt_plus	1,69	1.0
beta_wt_plus	2,69	1.0
beta_wt_plus	3,69	1.0
beta_wt_plus	4,69	1.0
beta_wt_plus	5,69	1.0
beta_wt_plus	1,70	1.0
beta_wt_plus	2,70	1.0
beta_wt_plus	3,70	1.0
beta_wt_plus	4,70	1.0
beta_wt_plus	5,70	1.0
beta_wt_plus	1,71	1.0
beta_wt_plus	2,71	1.0
beta_wt_plus	3,71	1.0
beta_wt_plus	4,71	1.0
beta_wt_plus	5,71	1.0
beta_wt_plus	1,72	1.0
beta_wt_plus	2,72	1.0
beta_wt_plus	3,72	1.0
beta_wt_plus	4,72	1.0
beta_wt_plus	5,72	1.0
beta_wt_plus	1,73	1.0
beta_wt_plus	2,73	1.0
beta_wt_plus	3,73	1.0
beta_wt_plus	4,73	1.0
beta_wt_plus	5,73	1.0
beta_wt_plus	1,74	1.0
beta_wt_plus	2,74	1.0
beta_wt_plus	3,74	1.0
beta_wt_plus	4,74	1.0
beta_wt_plus	5,74	1.0
beta_wt_plus	1,75	1.0
beta_wt_plus	2,75	1.0
beta_wt_plus	3,75	1.0
beta_wt_plus	4,75	1.0
beta_wt_plus	5,75	1.0
beta_wt_plus	1,76	1.0
beta_wt_plus	2,76	1.0
beta_wt_plus	3,76	1.0
beta_wt_plus	4,76	1.0
beta_wt_plus	5,76	1.0
beta_wt_plus	1,77	1.0
beta_wt_plus	2,77	1.0
beta_wt_plus	3,77	1.0
beta_wt_plus	4,77	1.0
beta_wt_plus	5,77	1.0
beta_wt_plus	1,78	1.0
beta_wt_plus	2,78	1.0
beta_wt_plus	3,78	1.0
beta_wt_plus	4,78	1.0
beta_wt_plus	5,78	1.0
beta_wt_plus	1,79	1.0
beta_wt_plus	2,79	1.0
beta_wt_plus	3,79	1.0
beta_wt_plus	4,79	1.0
beta_wt_plus	5,79	1.0
beta_wt_plus	1,80	1.0
beta_wt_plus	2,80	1.0
beta_wt_plus	3,80	1.0
beta_wt_plus	4,80	1.0
beta_wt_plus	5,80	1.0
beta_wt_plus	1,81	1.0
beta_wt_plus	2,81	1.0
beta_wt_plus	3,81	1.0
beta_wt_plus	4,81	1.0
beta_wt_plus	5,81	1.0
beta_wt_plus	1,82	1.0
beta_wt_plus	2,82	1.0
beta_wt_plus	3,82	1.0
beta_wt_plus	4,82	1.0
beta_wt_plus	5,82	1.0
beta_wt_plus	1,83	1.0
beta_wt_plus	2,83	1.0
beta_wt_plus	3,83	1.0
beta_wt_plus	4,83	1.0
beta_wt_plus	5,83	1.0
beta_wt_plus	1,84	1.0
beta_wt_plus	2,84	1.0
beta_wt_plus	3,84	1.0
beta_wt_plus	4,84	1.0
beta_wt_plus	5,84	1.0
beta_wt_plus	1,85	1.0
beta_wt_plus	2,85	1.0
beta_wt_plus	3,85	1.0
beta_wt_plus	4,85	1.0
beta_wt_plus	5,85	1.0
beta_wt_plus	1,86	1.0
beta_wt_plus	2,86	1.0
beta_wt_plus	3,86	1.0
beta_wt_plus	4,86	1.0
beta_wt_plus	5,86	1.0
beta_wt_plus	1,87	1.0
beta_wt_plus	2,87	1.0
beta_wt_plus	3,87	1.0
beta_wt_plus	4,87	1.0
beta_wt_plus	5,87	1.0
beta_wt_plus	1,88	1.0
beta_wt_plus	2,88	1.0
beta_wt_plus	3,88	1.0
beta_wt_plus	4,88	1.0
beta_wt_plus	5,88	1.0
beta_wt_plus	1,89	1.0
beta_wt_plus	2,89	1.0
beta_wt_plus	3,89	1.0
beta_wt_plus	4,89	1.0
beta_wt_plus	5,89	1.0
beta_wt_plus	1,90	1.0
beta_wt_plus	2,90	1.0
beta_wt_plus	3,90	1.0
beta_wt_plus	4,90	1.0
beta_wt_plus	5,90	1.0
beta_wt_plus	1,91	1.0
beta_wt_plus	2,91	1.0
beta_wt_plus	3,91	1.0
beta_wt_plus	4,91	1.0
beta_wt_plus	5,91	1.0
beta_wt_plus	1,92	1.0
beta_wt_plus	2,92	1.0
beta_wt_plus	3,92	1.0
beta_wt_plus	4,92	1.0
beta_wt_plus	5,92	1.0
beta_wt_plus	1,93	1.0
beta_wt_plus	2,93	1.0
beta_wt_plus	3,93	1.0
beta_wt_plus	4,93	1.0
beta_wt_plus	5,93	1.0
beta_wt_plus	1,94	1.0
beta_wt_plus	2,94	1.0
beta_wt_plus	3,94	1.0
beta_wt_plus	4,94	1.0
beta_wt_plus	5,94	1.0
beta_wt_plus	1,95	1.0
beta_wt_plus	2,95	1.0
beta_wt_plus	3,95	1.0
beta_wt_plus	4,95	1.0
beta_wt_plus	5,95	1.0
beta_wt_plus	1,96	1.0
beta_wt_plus	2,96	1.0
beta_wt_plus	3,96	1.0
beta_wt_plus	4,96	1.0
beta_wt_plus	5,96	1.0
omega_p_minus	scalar	-0.0
omega_p_plus	scalar	1.0
omega_u_minus	scalar	-0.0
omega_u_plus	scalar	1.0
psi_minus	1,1	0.0
psi_minus	2,1	0.0
psi_minus	3,1	0.0
psi_minus	4,1	0.0
psi_minus	5,1	0.0
psi_minus	6,1	0.0
psi_minus	7,1	0.0
psi_minus	8,1	0.0
psi_minus	9,1	0.0
psi_minus	10,1	0.0
psi_minus	11,1	0.0
psi_minus	12,1	0.0
psi_minus	13,1	0.0
psi_minus	14,1	0.0
psi_minus	15,1	0.0
psi_minus	16,1	0.0
psi_minus	17,1	0.0
psi_minus	18,1	0.0
psi_minus	19,1	0.0
psi_minus	20,1	0.0
psi_minus	1,2	0.0
psi_minus	2,2	0.0
psi_minus	3,2	0.0
psi_minus	4,2	0.0
psi_minus	5,2	0.0
psi_minus	6,2	0.0
psi_minus	7,2	0.0
psi_minus	8,2	0.0
psi_minus	9,2	0.0
psi_minus	10,2	0.0
psi_minus	11,2	0.0
psi_minus	12,2	0.0
psi_minus	13,2	0.0
psi_minus	14,2	0.0
psi_minus	15,2	0.0
psi_minus	16,2	0.0
psi_minus	17,2	0.0
psi_minus	18,2	0.0
psi_minus	19,2	0.0
psi_minus	20,2	0.0
psi_minus	1,3	0.0
psi_minus	2,3	0.0
psi_minus	3,3	0.0
psi_minus	4,3	0.0
psi_minus	5,3	0.0
psi_minus	6,3	0.0
psi_minus	7,3	0.0
psi_minus	8,3	0.0
psi_minus	9,3	0.0
psi_minus	10,3	0.0
psi_minus	11,3	0.0
psi_minus	12,3	0.0
psi_minus	13,3	0.0
psi_minus	14,3	0.0
psi_minus	15,3	0.0
psi_minus	16,3	0.0
psi_minus	17,3	0.0
psi_minus	18,3	0.0
psi_minus	19,3	0.0
psi_minus	20,3	0.0
psi_minus	1,4	0.0
psi_minus	2,4	0.0
psi_minus	3,4	0.0
psi_minus	4,4	0.0
psi_minus	5,4	0.0
psi_minus	6,4	0.0
psi_minus	7,4	0.0
psi_minus	8,4	0.0
psi_minus	9,4	0.0
psi_minus	10,4	0.0
psi_minus	11,4	0.0
psi_minus	12,4	0.0
psi_minus	13,4	0.0
psi_minus	14,4	0.0
psi_minus	15,4	0.0
psi_minus	16,4	0.0
psi_minus	17,4	0.0
psi_minus	18,4	0.0
psi_minus	19,4	0.0
psi_minus	20,4	0.0
psi_minus	1,5	0.0
psi_minus	2,5	0.0
psi_minus	3,5	0.0
psi_minus	4,5	0.0
psi_minus	5,5	0.0
psi_minus	6,5	0.0
psi_minus	7,5	0.0
psi_minus	8,5	0.0
psi_minus	9,5	0.0
psi_minus	10,5	0.0
psi_minus	11,5	0.0
psi_minus	12,5	0.0
psi_minus	13,5	0.0
psi_minus	14,5	0.0
psi_minus	15,5	0.0
psi_minus	16,5	0.0
psi_minus	17,5	0.0
psi_minus	18,5	0.0
psi_minus	19,5	0.0
psi_minus	20,5	0.0
psi_minus	1,6	0.0
psi_minus	2,6	0.0
psi_minus	3,6	0.0
psi_minus	4,6	0.0
psi_minus	5,6	0.0
psi_minus	6,6	0.0
psi_minus	7,6	0.0
psi_minus	8,6	0.0
psi_minus	9,6	0.0
psi_minus	10,6	0.0
psi_minus	11,6	0.0
psi_minus	12,6	0.0
psi_minus	13,6	0.0
psi_minus	14,6	0.0
psi_minus	15,6	0.0
psi_minus	16,6	0.0
psi_minus	17,6	0.0
psi_minus	18,6	0.0
psi_minus	19,6	0.0
psi_minus	20,6	0.0
psi_minus	1,7	-0.0
psi_minus	2,7	0.0
psi_minus	3,7	-0.0
psi_minus	4,7	0.0
psi_minus	5,7	0.0
psi_minus	6,7	0.0
psi_minus	7,7	0.0
psi_minus	8,7	-0.0
psi_minus	9,7	-0.0
psi_minus	10,7	-0.0
psi_minus	11,7	0.0
psi_minus	12,7	0.0
psi_minus	13,7	0.0
psi_minus	14,7	-0.0
psi_minus	15,7	0.0
psi_minus	16,7	-0.0
psi_minus	17,7	-0.0
psi_minus	18,7	0.0
psi_minus	19,7	0.0
psi_minus	20,7	-0.0
psi_minus	1,8	-0.0
psi_minus	2,8	0.0
psi_minus	3,8	-0.0
psi_minus	4,8	0.0
psi_minus	5,8	0.0
psi_minus	6,8	0.0
psi_minus	7,8	0.0
psi_minus	8,8	-0.0
psi_minus	9,8	-0.0
psi_minus	10,8	-0.0
psi_minus	11,8	0.0
psi_minus	12,8	0.0
psi_minus	13,8	0.0
psi_minus	14,8	-0.0
psi_minus	15,8	0.0
psi_minus	16,8	-0.0
psi_minus	17,8	-0.0
psi_minus	18,8	0.0
psi_minus	19,8	0.0
psi_minus	20,8	-0.0
psi_minus	1,9	-0.0
psi_minus	2,9	0.0
psi_minus	3,9	-0.0
psi_minus	4,9	0.0
psi_minus	5,9	0.0
psi_minus	6,9	0.0
psi_minus	7,9	0.0
psi_minus	8,9	-0.0
psi_minus	9,9	-0.0
psi_minus	10,9	-0.0
psi_minus	11,9	0.0
psi_minus	12,9	0.0
psi_minus	13,9	0.0
psi_minus	14,9	-0.0
psi_minus	15,9	0.0
psi_minus	16,9	-0.0
psi_minus	17,9	-0.0
psi_minus	18,9	0.0
psi_minus	19,9	0.0
psi_minus	20,9	-0.0
psi_minus	1,10	-0.0
psi_minus	2,10	0.0
psi_minus	3,10	-0.0
psi_minus	4,10	0.0
psi_minus	5,10	0.0
psi_minus	6,10	0.0
psi_minus	7,10	0.0
psi_minus	8,10	-0.0
psi_minus	9,10	-0.0
psi_minus	10,10	-0.0
psi_minus	11,10	0.0
psi_minus	12,10	0.0
psi_minus	13,10	0.0
psi_minus	14,10	-0.0
psi_minus	15,10	0.0
psi_minus	16,10	-0.0
psi_minus	17,10	-0.0
psi_minus	18,10	0.0
psi_minus	19,10	0.0
psi_minus	20,10	-0.0
psi_minus	1,11	-0.0
psi_minus	2,11	0.0
psi_minus	3,11	-0.0
psi_minus	4,11	0.0
psi_minus	5,11	0.0
psi_minus	6,11	0.0
psi_minus	7,11	0.0
psi_minus	8,11	-0.0
psi_minus	9,11	-0.0
psi_minus	10,11	-0.0
psi_minus	11,11	0.0
psi_minus	12,11	0.0
psi_minus	13,11	0.0
psi_minus	14,11	-0.0
psi_minus	15,11	0.0
psi_minus	16,11	-0.0
psi_minus	17,11	-0.0
psi_minus	18,11	0.0
psi_minus	19,11	0.0
psi_minus	20,11	-0.0
psi_minus	1,12	-0.0
psi_minus	2,12	0.0
psi_minus	3,12	-0.0
psi_minus	4,12	0.0
psi_minus	5,12	0.0
psi_minus	6,12	0.0
psi_minus	7,12	0.0
psi_minus	8,12	-0.0
psi_minus	9,12	-0.0
psi_minus	10,12	-0.0
psi_minus	11,12	0.0
psi_minus	12,12	0.0
psi_minus	13,12	0.0
psi_minus	14,12	-0.0
psi_minus	15,12	0.0
psi_minus	16,12	-0.0
psi_minus	17,12	-0.0
psi_minus	18,12	0.0
psi_minus	19,12	0.0
psi_minus	20,12	-0.0
psi_minus	1,13	-0.0
psi_minus	2,13	0.0
psi_minus	3,13	-0.0
psi_minus	4,13	0.0
psi_minus	5,13	0.0
psi_minus	6,13	0.0
psi_minus	7,13	0.0
psi_minus	8,13	-0.0
psi_minus	9,13	-0.0
psi_minus	10,13	-0.0
psi_minus	11,13	0.0
psi_minus	12,13	0.0
psi_minus	13,13	0.0
psi_minus	14,13	-0.0
psi_minus	15,13	0.0
psi_minus	16,13	-0.0
psi_minus	17,13	-0.0
psi_minus	18,13	0.0
psi_minus	19,13	0.0
psi_minus	20,13	-0.0
psi_minus	1,14	-0.0
psi_minus	2,14	0.0
psi_minus	3,14	-0.0
psi_minus	4,14	0.0
psi_minus	5,14	0.0
psi_minus	6,14	0.0
psi_minus	7,14	0.0
psi_minus	8,14	-0.0
psi_minus	9,14	-0.0
psi_minus	10,14	-0.0
psi_minus	11,14	0.0
psi_minus	12,14	0.0
psi_minus	13,14	0.0
psi_minus	14,14	-0.0
psi_minus	15,14	0.0
psi_minus	16,14	-0.0
psi_minus	17,14	-0.0
psi_minus	18,14	0.0
psi_minus	19,14	0.0
psi_minus	20,14	-0.0
psi_minus	1,15	-0.0
psi_minus	2,15	0.0
psi_minus	3,15	-0.0
psi_minus	4,15	0.0
psi_minus	5,15	0.0
psi_minus	6,15	0.0
psi_minus	7,15	0.0
psi_minus	8,15	-0.0
psi_minus	9,15	-0.0
psi_minus	10,15	-0.0
psi_minus	11,15	0.0
psi_minus	12,15	0.0
psi_minus	13,15	0.0
psi_minus	14,15	-0.0
psi_minus	15,15	0.0
psi_minus	16,15	-0.0
psi_minus	17,15	-0.0
psi_minus	18,15	0.0
psi_minus	19,15	0.0
psi_minus	20,15	-0.0
psi_minus	1,16	-0.0
psi_minus	2,16	0.0
psi_minus	3,16	-0.0
psi_minus	4,16	0.0
psi_minus	5,16	0.0
psi_minus	6,16	0.0
psi_minus	7,16	0.0
psi_minus	8,16	-0.0
psi_minus	9,16	-0.0
psi_minus	10,16	-0.0
psi_minus	11,16	0.0
psi_minus	12,16	0.0
psi_minus	13,16	0.0
psi_minus	14,16	-0.0
psi_minus	15,16	0.0
psi_minus	16,16	-0.0
psi_minus	17,16	-0.0
psi_minus	18,16	0.0
psi_minus	19,16	0.0
psi_minus	20,16	-0.0
psi_minus	1,17	-0.0
psi_minus	2,17	0.0
psi_minus	3,17	-0.0
psi_minus	4,17	0.0
psi_minus	5,17	0.0
psi_minus	6,17	0.0
psi_minus	7,17	0.0
psi_minus	8,17	-0.0
psi_minus	9,17	-0.0
psi_minus	10,17	-0.0
psi_minus	11,17	0.0
psi_minus	12,17	0.0
psi_minus	13,17	0.0
psi_minus	14,17	-0.0
psi_minus	15,17	0.0
psi_minus	16,17	-0.0
psi_minus	17,17	-0.0
psi_minus	18,17	0.0
psi_minus	19,17	0.0
psi_minus	20,17	-0.0
psi_minus	1,18	-0.0
psi_minus	2,18	0.0
psi_minus	3,18	-0.0
psi_minus	4,18	0.0
psi_minus	5,18	0.0
psi_minus	6,18	0.0
psi_minus	7,18	0.0
psi_minus	8,18	-0.0
psi_minus	9,18	-0.0
psi_minus	10,18	-0.0
psi_minus	11,18	0.0
psi_minus	12,18	0.0
psi_minus	13,18	0.0
psi_minus	14,18	-0.0
psi_minus	15,18	0.0
psi_minus	16,18	-0.0
psi_minus	17,18	-0.0
psi_minus	18,18	0.0
psi_minus	19,18	0.0
psi_minus	20,18	-0.0
psi_minus	1,19	-0.0
psi_minus	2,19	0.0
psi_minus	3,19	-0.0
psi_minus	4,19	0.0
psi_minus	5,19	0.0
psi_minus	6,19	0.0
psi_minus	7,19	0.0
psi_minus	8,19	-0.0
psi_minus	9,19	-0.0
psi_minus	10,19	-0.0
psi_minus	11,19	0.0
psi_minus	12,19	0.0
psi_minus	13,19	0.0
psi_minus	14,19	-0.0
psi_minus	15,19	0.0
psi_minus	16,19	-0.0
psi_minus	17,19	-0.0
psi_minus	18,19	0.0
psi_minus	19,19	0.0
psi_minus	20,19	-0.0
psi_minus	1,20	-0.0
psi_minus	2,20	0.0
psi_minus	3,20	-0.0
psi_minus	4,20	0.0
psi_minus	5,20	0.0
psi_minus	6,20	0.0
psi_minus	7,20	0.0
psi_minus	8,20	-0.0
psi_minus	9,20	-0.0
psi_minus	10,20	-0.0
psi_minus	11,20	0.0
psi_minus	12,20	0.0
psi_minus	13,20	0.0
psi_minus	14,20	-0.0
psi_minus	15,20	0.0
psi_minus	16,20	-0.0
psi_minus	17,20	-0.0
psi_minus	18,20	0.0
psi_minus	19,20	0.0
psi_minus	20,20	-0.0
psi_minus	1,21	0.0
psi_minus	2,21	0.0
psi_minus	3,21	0.0
psi_minus	4,21	0.0
psi_minus	5,21	0.0
psi_minus	6,21	0.0
psi_minus	7,21	0.0
psi_minus	8,21	0.0
psi_minus	9,21	0.0
psi_minus	10,21	0.0
psi_minus	11,21	0.0
psi_minus	12,21	0.0
psi_minus	13,21	0.0
psi_minus	14,21	0.0
psi_minus	15,21	0.0
psi_minus	16,21	0.0
psi_minus	17,21	0.0
psi_minus	18,21	0.0
psi_minus	19,21	0.0
psi_minus	20,21	0.0
psi_minus	1,22	0.0
psi_minus	2,22	0.0
psi_minus	3,22	0.0
psi_minus	4,22	0.0
psi_minus	5,22	0.0
psi_minus	6,22	0.0
psi_minus	7,22	0.0
psi_minus	8,22	0.0
psi_minus	9,22	0.0
psi_minus	10,22	0.0
psi_minus	11,22	0.0
psi_minus	12,22	0.0
psi_minus	13,22	0.0
psi_minus	14,22	0.0
psi_minus	15,22	0.0
psi_minus	16,22	0.0
psi_minus	17,22	0.0
psi_minus	18,22	0.0
psi_minus	19,22	0.0
psi_minus	20,22	0.0
psi_minus	1,23	0.0
psi_minus	2,23	0.0
psi_minus	3,23	0.0
psi_minus	4,23	0.0
psi_minus	5,23	0.0
psi_minus	6,23	0.0
psi_minus	7,23	0.0
psi_minus	8,23	0.0
psi_minus	9,23	0.0
psi_minus	10,23	0.0
psi_minus	11,23	0.0
psi_minus	12,23	0.0
psi_minus	13,23	0.0
psi_minus	14,23	0.0
psi_minus	15,23	0.0
psi_minus	16,23	0.0
psi_minus	17,23	0.0
psi_minus	18,23	0.0
psi_minus	19,23	0.0
psi_minus	20,23	0.0
psi_minus	1,24	0.0
psi_minus	2,24	0.0
psi_minus	3,24	0.0
psi_minus	4,24	0.0
psi_minus	5,24	0.0
psi_minus	6,24	0.0
psi_minus	7,24	0.0
psi_minus	8,24	0.0
psi_minus	9,24	0.0
psi_minus	10,24	0.0
psi_minus	11,24	0.0
psi_minus	12,24	0.0
psi_minus	13,24	0.0
psi_minus	14,24	0.0
psi_minus	15,24	0.0
psi_minus	16,24	0.0
psi_minus	17,24	0.0
psi_minus	18,24	0.0
psi_minus	19,24	0.0
psi_minus	20,24	0.0
psi_minus	1,25	0.0
psi_minus	2,25	0.0
psi_minus	3,25	0.0
psi_minus	4,25	0.0
psi_minus	5,25	0.0
psi_minus	6,25	0.0
psi_minus	7,25	0.0
psi_minus	8,25	0.0
psi_minus	9,25	0.0
psi_minus	10,25	0.0
psi_minus	11,25	0.0
psi_minus	12,25	0.0
psi_minus	13,25	0.0
psi_minus	14,25	0.0
psi_minus	15,25	0.0
psi_minus	16,25	0.0
psi_minus	17,25	0.0
psi_minus	18,25	0.0
psi_minus	19,25	0.0
psi_minus	20,25	0.0
psi_minus	1,26	0.0
psi_minus	2,26	0.0
psi_minus	3,26	0.0
psi_minus	4,26	0.0
psi_minus	5,26	0.0
psi_minus	6,26	0.0
psi_minus	7,26	0.0
psi_minus	8,26	0.0
psi_minus	9,26	0.0
psi_minus	10,26	0.0
psi_minus	11,26	0.0
psi_minus	12,26	0.0
psi_minus	13,26	0.0
psi_minus	14,26	0.0
psi_minus	15,26	0.0
psi_minus	16,26	0.0
psi_minus	17,26	0.0
psi_minus	18,26	0.0
psi_minus	19,26	0.0
psi_minus	20,26	0.0
psi_minus	1,27	0.0
psi_minus	2,27	0.0
psi_minus	3,27	0.0
psi_minus	4,27	0.0
psi_minus	5,27	0.0
psi_minus	6,27	0.0
psi_minus	7,27	0.0
psi_minus	8,27	0.0
psi_minus	9,27	0.0
psi_minus	10,27	0.0
psi_minus	11,27	0.0
psi_minus	12,27	0.0
psi_minus	13,27	0.0
psi_minus	14,27	0.0
psi_minus	15,27	0.0
psi_minus	16,27	0.0
psi_minus	17,27	0.0
psi_minus	18,27	0.0
psi_minus	19,27	0.0
psi_minus	20,27	0.0
psi_minus	1,28	0.0
psi_minus	2,28	0.0
psi_minus	3,28	0.0
psi_minus	4,28	0.0
psi_minus	5,28	0.0
psi_minus	6,28	0.0
psi_minus	7,28	0.0
psi_minus	8,28	0.0
psi_minus	9,28	0.0
psi_minus	10,28	0.0
psi_minus	11,28	0.0
psi_minus	12,28	0.0
psi_minus	13,28	0.0
psi_minus	14,28	0.0
psi_minus	15,28	0.0
psi_minus	16,28	0.0
psi_minus	17,28	0.0
psi_minus	18,28	0.0
psi_minus	19,28	0.0
psi_minus	20,28	0.0
psi_minus	1,29	0.0
psi_minus	2,29	0.0
psi_minus	3,29	0.0
psi_minus	4,29	0.0
psi_minus	5,29	0.0
psi_minus	6,29	0.0
psi_minus	7,29	0.0
psi_minus	8,29	0.0
psi_minus	9,29	0.0
psi_minus	10,29	0.0
psi_minus	11,29	0.0
psi_minus	12,29	0.0
psi_minus	13,29	0.0
psi_minus	14,29	0.0
psi_minus	15,29	0.0
psi_minus	16,29	0.0
psi_minus	17,29	0.0
psi_minus	18,29	0.0
psi_minus	19,29	0.0
psi_minus	20,29	0.0
psi_minus	1,30	0.0
psi_minus	2,30	0.0
psi_minus	3,30	0.0
psi_minus	4,30	0.0
psi_minus	5,30	0.0
psi_minus	6,30	0.0
psi_minus	7,30	0.0
psi_minus	8,30	0.0
psi_minus	9,30	0.0
psi_minus	10,30	0.0
psi_minus	11,30	0.0
psi_minus	12,30	0.0
psi_minus	13,30	0.0
psi_minus	14,30	0.0
psi_minus	15,30	0.0
psi_minus	16,30	0.0
psi_minus	17,30	0.0
psi_minus	18,30	0.0
psi_minus	19,30	0.0
psi_minus	20,30	0.0
psi_minus	1,31	-0.0
psi_minus	2,31	0.0
psi_minus	3,31	-0.0
psi_minus	4,31	0.0
psi_minus	5,31	0.0
psi_minus	6,31	0.0
psi_minus	7,31	0.0
psi_minus	8,31	-0.0
psi_minus	9,31	-0.0
psi_minus	10,31	-0.0
psi_minus	11,31	0.0
psi_minus	12,31	0.0
psi_minus	13,31	0.0
psi_minus	14,31	-0.0
psi_minus	15,31	0.0
psi_minus	16,31	-0.0
psi_minus	17,31	-0.0
psi_minus	18,31	0.0
psi_minus	19,31	0.0
psi_minus	20,31	-0.0
psi_minus	1,32	-0.0
psi_minus	2,32	0.0
psi_minus	3,32	-0.0
psi_minus	4,32	0.0
psi_minus	5,32	0.0
psi_minus	6,32	0.0
psi_minus	7,32	0.0
psi_minus	8,32	-0.0
psi_minus	9,32	-0.0
psi_minus	10,32	-0.0
psi_minus	11,32	0.0
psi_minus	12,32	0.0
psi_minus	13,32	0.0
psi_minus	14,32	-0.0
psi_minus	15,32	0.0
psi_minus	16,32	-0.0
psi_minus	17,32	-0.0
psi_minus	18,32	0.0
psi_minus	19,32	0.0
psi_minus	20,32	-0.0
psi_minus	1,33	-0.0
psi_minus	2,33	0.0
psi_minus	3,33	-0.0
psi_minus	4,33	0.0
psi_minus	5,33	0.0
psi_minus	6,33	0.0
psi_minus	7,33	0.0
psi_minus	8,33	-0.0
psi_minus	9,33	-0.0
psi_minus	10,33	-0.0
psi_minus	11,33	0.0
psi_minus	12,33	0.0
psi_minus	13,33	0.0
psi_minus	14,33	-0.0
psi_minus	15,33	0.0
psi_minus	16,33	-0.0
psi_minus	17,33	-0.0
psi_minus	18,33	0.0
psi_minus	19,33	0.0
psi_minus	20,33	-0.0
psi_minus	1,34	-0.0
psi_minus	2,34	0.0
psi_minus	3,34	-0.0
psi_minus	4,34	0.0
psi_minus	5,34	0.0
psi_minus	6,34	0.0
psi_minus	7,34	0.0
psi_minus	8,34	-0.0
psi_minus	9,34	-0.0
psi_minus	10,34	-0.0
psi_minus	11,34	0.0
psi_minus	12,34	0.0
psi_minus	13,34	0.0
psi_minus	14,34	-0.0
psi_minus	15,34	0.0
psi_minus	16,34	-0.0
psi_minus	17,34	-0.0
psi_minus	18,34	0.0
psi_minus	19,34	0.0
psi_minus	20,34	-0.0
psi_minus	1,35	-0.0
psi_minus	2,35	0.0
psi_minus	3,35	-0.0
psi_minus	4,35	0.0
psi_minus	5,35	0.0
psi_minus	6,35	0.0
psi_minus	7,35	0.0
psi_minus	8,35	-0.0
psi_minus	9,35	-0.0
psi_minus	10,35	-0.0
psi_minus	11,35	0.0
psi_minus	12,35	0.0
psi_minus	13,35	0.0
psi_minus	14,35	-0.0
psi_minus	15,35	0.0
psi_minus	16,35	-0.0
psi_minus	17,35	-0.0
psi_minus	18,35	0.0
psi_minus	19,35	0.0
psi_minus	20,35	-0.0
psi_minus	1,36	-0.0
psi_minus	2,36	0.0
psi_minus	3,36	-0.0
psi_minus	4,36	0.0
psi_minus	5,36	0.0
psi_minus	6,36	0.0
psi_minus	7,36	0.0
psi_minus	8,36	-0.0
psi_minus	9,36	-0.0
psi_minus	10,36	-0.0
psi_minus	11,36	0.0
psi_minus	12,36	0.0
psi_minus	13,36	0.0
psi_minus	14,36	-0.0
psi_minus	15,36	0.0
psi_minus	16,36	-0.0
psi_minus	17,36	-0.0
psi_minus	18,36	0.0
psi_minus	19,36	0.0
psi_minus	20,36	-0.0
psi_minus	1,37	-0.0
psi_minus	2,37	0.0
psi_minus	3,37	-0.0
psi_minus	4,37	0.0
psi_minus	5,37	0.0
psi_minus	6,37	0.0
psi_minus	7,37	0.0
psi_minus	8,37	-0.0
psi_minus	9,37	-0.0
psi_minus	10,37	-0.0
psi_minus	11,37	0.0
psi_minus	12,37	0.0
psi_minus	13,37	0.0
psi_minus	14,37	-0.0
psi_minus	15,37	0.0
psi_minus	16,37	-0.0
psi_minus	17,37	-0.0
psi_minus	18,37	0.0
psi_minus	19,37	0.0
psi_minus	20,37	-0.0
psi_minus	1,38	-0.0
psi_minus	2,38	0.0
psi_minus	3,38	-0.0
psi_minus	4,38	0.0
psi_minus	5,38	0.0
psi_minus	6,38	0.0
psi_minus	7,38	0.0
psi_minus	8,38	-0.0
psi_minus	9,38	-0.0
psi_minus	10,38	-0.0
psi_minus	11,38	0.0
psi_minus	12,38	0.0
psi_minus	13,38	0.0
psi_minus	14,38	-0.0
psi_minus	15,38	0.0
psi_minus	16,38	-0.0
psi_minus	17,38	-0.0
psi_minus	18,38	0.0
psi_minus	19,38	0.0
psi_minus	20,38	-0.0
psi_minus	1,39	-0.0
psi_minus	2,39	0.0
psi_minus	3,39	-0.0
psi_minus	4,39	0.0
psi_minus	5,39	0.0
psi_minus	6,39	0.0
psi_minus	7,39	0.0
psi_minus	8,39	-0.0
psi_minus	9,39	-0.0
psi_minus	10,39	-0.0
psi_minus	11,39	0.0
psi_minus	12,39	0.0
psi_minus	13,39	0.0
psi_minus	14,39	-0.0
psi_minus	15,39	0.0
psi_minus	16,39	-0.0
psi_minus	17,39	-0.0
psi_minus	18,39	0.0
psi_minus	19,39	0.0
psi_minus	20,39	-0.0
psi_minus	1,40	-0.0
psi_minus	2,40	0.0
psi_minus	3,40	-0.0
psi_minus	4,40	0.0
psi_minus	5,40	0.0
psi_minus	6,40	0.0
psi_minus	7,40	0.0
psi_minus	8,40	-0.0
psi_minus	9,40	-0.0
psi_minus	10,40	-0.0
psi_minus	11,40	0.0
psi_minus	12,40	0.0
psi_minus	13,40	0.0
psi_minus	14,40	-0.0
psi_minus	15,40	0.0
psi_minus	16,40	-0.0
psi_minus	17,40	-0.0
psi_minus	18,40	0.0
psi_minus	19,40	0.0
psi_minus	20,40	-0.0
psi_minus	1,41	-0.0
psi_minus	2,41	0.0
psi_minus	3,41	-0.0
psi_minus	4,41	0.0
psi_minus	5,41	0.0
psi_minus	6,41	0.0
psi_minus	7,41	0.0
psi_minus	8,41	-0.0
psi_minus	9,41	-0.0
psi_minus	10,41	-0.0
psi_minus	11,41	0.0
psi_minus	12,41	0.0
psi_minus	13,41	0.0
psi_minus	14,41	-0.0
psi_minus	15,41	0.0
psi_minus	16,41	-0.0
psi_minus	17,41	-0.0
psi_minus	18,41	0.0
psi_minus	19,41	0.0
psi_minus	20,41	-0.0
psi_minus	1,42	-0.0
psi_minus	2,42	0.0
psi_minus	3,42	-0.0
psi_minus	4,42	0.0
psi_minus	5,42	0.0
psi_minus	6,42	0.0
psi_minus	7,42	0.0
psi_minus	8,42	-0.0
psi_minus	9,42	-0.0
psi_minus	10,42	-0.0
psi_minus	11,42	0.0
psi_minus	12,42	0.0
psi_minus	13,42	0.0
psi_minus	14,42	-0.0
psi_minus	15,42	0.0
psi_minus	16,42	-0.0
psi_minus	17,42	-0.0
psi_minus	18,42	0.0
psi_minus	19,42	0.0
psi_minus	20,42	-0.0
psi_minus	1,43	-0.0
psi_minus	2,43	0.0
psi_minus	3,43	-0.0
psi_minus	4,43	0.0
psi_minus	5,43	0.0
psi_minus	6,43	0.0
psi_minus	7,43	0.0
psi_minus	8,43	-0.0
psi_minus	9,43	-0.0
psi_minus	10,43	-0.0
psi_minus	11,43	0.0
psi_minus	12,43	0.0
psi_minus	13,43	0.0
psi_minus	14,43	-0.0
psi_minus	15,43	0.0
psi_minus	16,43	-0.0
psi_minus	17,43	-0.0
psi_minus	18,43	0.0
psi_minus	19,43	0.0
psi_minus	20,43	-0.0
psi_minus	1,44	-0.0
psi_minus	2,44	0.0
psi_minus	3,44	-0.0
psi_minus	4,44	0.0
psi_minus	5,44	0.0
psi_minus	6,44	0.0
psi_minus	7,44	0.0
psi_minus	8,44	-0.0
psi_minus	9,44	-0.0
psi_minus	10,44	-0.0
psi_minus	11,44	0.0
psi_minus	12,44	0.0
psi_minus	13,44	0.0
psi_minus	14,44	-0.0
psi_minus	15,44	0.0
psi_minus	16,44	-0.0
psi_minus	17,44	-0.0
psi_minus	18,44	0.0
psi_minus	19,44	0.0
psi_minus	20,44	-0.0
psi_minus	1,45	0.0
psi_minus	2,45	0.0
psi_minus	3,45	0.0
psi_minus	4,45	0.0
psi_minus	5,45	0.0
psi_minus	6,45	0.0
psi_minus	7,45	0.0
psi_minus	8,45	0.0
psi_minus	9,45	0.0
psi_minus	10,45	0.0
psi_minus	11,45	0.0
psi_minus	12,45	0.0
psi_minus	13,45	0.0
psi_minus	14,45	0.0
psi_minus	15,45	0.0
psi_minus	16,45	0.0
psi_minus	17,45	0.0
psi_minus	18,45	0.0
psi_minus	19,45	0.0
psi_minus	20,45	0.0
psi_minus	1,46	0.0
psi_minus	2,46	0.0
psi_minus	3,46	0.0
psi_minus	4,46	0.0
psi_minus	5,46	0.0
psi_minus	6,46	0.0
psi_minus	7,46	0.0
psi_minus	8,46	0.0
psi_minus	9,46	0.0
psi_minus	10,46	0.0
psi_minus	11,46	0.0
psi_minus	12,46	0.0
psi_minus	13,46	0.0
psi_minus	14,46	0.0
psi_minus	15,46	0.0
psi_minus	16,46	0.0
psi_minus	17,46	0.0
psi_minus	18,46	0.0
psi_minus	19,46	0.0
psi_minus	20,46	0.0
psi_minus	1,47	0.0
psi_minus	2,47	0.0
psi_minus	3,47	0.0
psi_minus	4,47	0.0
psi_minus	5,47	0.0
psi_minus	6,47	0.0
psi_minus	7,47	0.0
psi_minus	8,47	0.0
psi_minus	9,47	0.0
psi_minus	10,47	0.0
psi_minus	11,47	0.0
psi_minus	12,47	0.0
psi_minus	13,47	0.0
psi_minus	14,47	0.0
psi_minus	15,47	0.0
psi_minus	16,47	0.0
psi_minus	17,47	0.0
psi_minus	18,47	0.0
psi_minus	19,47	0.0
psi_minus	20,47	0.0
psi_minus	1,48	0.0
psi_minus	2,48	0.0
psi_minus	3,48	0.0
psi_minus	4,48	0.0
psi_minus	5,48	0.0
psi_minus	6,48	0.0
psi_minus	7,48	0.0
psi_minus	8,48	0.0
psi_minus	9,48	0.0
psi_minus	10,48	0.0
psi_minus	11,48	0.0
psi_minus	12,48	0.0
psi_minus	13,48	0.0
psi_minus	14,48	0.0
psi_minus	15,48	0.0
psi_minus	16,48	0.0
psi_minus	17,48	0.0
psi_minus	18,48	0.0
psi_minus	19,48	0.0
psi_minus	20,48	0.0
psi_minus	1,49	0.0
psi_minus	2,49	0.0
psi_minus	3,49	0.0
psi_minus	4,49	0.0
psi_minus	5,49	0.0
psi_minus	6,49	0.0
psi_minus	7,49	0.0
psi_minus	8,49	0.0
psi_minus	9,49	0.0
psi_minus	10,49	0.0
psi_minus	11,49	0.0
psi_minus	12,49	0.0
psi_minus	13,49	0.0
psi_minus	14,49	0.0
psi_minus	15,49	0.0
psi_minus	16,49	0.0
psi_minus	17,49	0.0
psi_minus	18,49	0.0
psi_minus	19,49	0.0
psi_minus	20,49	0.0
psi_minus	1,50	0.0
psi_minus	2,50	0.0
psi_minus	3,50	0.0
psi_minus	4,50	0.0
psi_minus	5,50	0.0
psi_minus	6,50	0.0
psi_minus	7,50	0.0
psi_minus	8,50	0.0
psi_minus	9,50	0.0
psi_minus	10,50	0.0
psi_minus	11,50	0.0
psi_minus	12,50	0.0
psi_minus	13,50	0.0
psi_minus	14,50	0.0
psi_minus	15,50	0.0
psi_minus	16,50	0.0
psi_minus	17,50	0.0
psi_minus	18,50	0.0
psi_minus	19,50	0.0
psi_minus	20,50	0.0
psi_minus	1,51	0.0
psi_minus	2,51	0.0
psi_minus	3,51	0.0
psi_minus	4,51	0.0
psi_minus	5,51	0.0
psi_minus	6,51	0.0
psi_minus	7,51	0.0
psi_minus	8,51	0.0
psi_minus	9,51	0.0
psi_minus	10,51	0.0
psi_minus	11,51	0.0
psi_minus	12,51	0.0
psi_minus	13,51	0.0
psi_minus	14,51	0.0
psi_minus	15,51	0.0
psi_minus	16,51	0.0
psi_minus	17,51	0.0
psi_minus	18,51	0.0
psi_minus	19,51	0.0
psi_minus	20,51	0.0
psi_minus	1,52	0.0
psi_minus	2,52	0.0
psi_minus	3,52	0.0
psi_minus	4,52	0.0
psi_minus	5,52	0.0
psi_minus	6,52	0.0
psi_minus	7,52	0.0
psi_minus	8,52	0.0
psi_minus	9,52	0.0
psi_minus	10,52	0.0
psi_minus	11,52	0.0
psi_minus	12,52	0.0
psi_minus	13,52	0.0
psi_minus	14,52	0.0
psi_minus	15,52	0.0
psi_minus	16,52	0.0
psi_minus	17,52	0.0
psi_minus	18,52	0.0
psi_minus	19,52	0.0
psi_minus	20,52	0.0
psi_minus	1,53	0.0
psi_minus	2,53	0.0
psi_minus	3,53	0.0
psi_minus	4,53	0.0
psi_minus	5,53	0.0
psi_minus	6,53	0.0
psi_minus	7,53	0.0
psi_minus	8,53	0.0
psi_minus	9,53	0.0
psi_minus	10,53	0.0
psi_minus	11,53	0.0
psi_minus	12,53	0.0
psi_minus	13,53	0.0
psi_minus	14,53	0.0
psi_minus	15,53	0.0
psi_minus	16,53	0.0
psi_minus	17,53	0.0
psi_minus	18,53	0.0
psi_minus	19,53	0.0
psi_minus	20,53	0.0
psi_minus	1,54	0.0
psi_minus	2,54	0.0
psi_minus	3,54	0.0
psi_minus	4,54	0.0
psi_minus	5,54	0.0
psi_minus	6,54	0.0
psi_minus	7,54	0.0
psi_minus	8,54	0.0
psi_minus	9,54	0.0
psi_minus	10,54	0.0
psi_minus	11,54	0.0
psi_minus	12,54	0.0
psi_minus	13,54	0.0
psi_minus	14,54	0.0
psi_minus	15,54	0.0
psi_minus	16,54	0.0
psi_minus	17,54	0.0
psi_minus	18,54	0.0
psi_minus	19,54	0.0
psi_minus	20,54	0.0
psi_minus	1,55	-0.0
psi_minus	2,55	0.0
psi_minus	3,55	-0.0
psi_minus	4,55	0.0
psi_minus	5,55	0.0
psi_minus	6,55	0.0
psi_minus	7,55	0.0
psi_minus	8,55	-0.0
psi_minus	9,55	-0.0
psi_minus	10,55	-0.0
psi_minus	11,55	0.0
psi_minus	12,55	0.0
psi_minus	13,55	0.0
psi_minus	14,55	-0.0
psi_minus	15,55	0.0
psi_minus	16,55	-0.0
psi_minus	17,55	-0.0
psi_minus	18,55	0.0
psi_minus	19,55	0.0
psi_minus	20,55	-0.0
psi_minus	1,56	-0.0
psi_minus	2,56	0.0
psi_minus	3,56	-0.0
psi_minus	4,56	0.0
psi_minus	5,56	0.0
psi_minus	6,56	0.0
psi_minus	7,56	0.0
psi_minus	8,56	-0.0
psi_minus	9,56	-0.0
psi_minus	10,56	-0.0
psi_minus	11,56	0.0
psi_minus	12,56	0.0
psi_minus	13,56	0.0
psi_minus	14,56	-0.0
psi_minus	15,56	0.0
psi_minus	16,56	-0.0
psi_minus	17,56	-0.0
psi_minus	18,56	0.0
psi_minus	19,56	0.0
psi_minus	20,56	-0.0
psi_minus	1,57	-0.0
psi_minus	2,57	0.0
psi_minus	3,57	-0.0
psi_minus	4,57	0.0
psi_minus	5,57	0.0
psi_minus	6,57	0.0
psi_minus	7,57	0.0
psi_minus	8,57	-0.0
psi_minus	9,57	-0.0
psi_minus	10,57	-0.0
psi_minus	11,57	0.0
psi_minus	12,57	0.0
psi_minus	13,57	0.0
psi_minus	14,57	-0.0
psi_minus	15,57	0.0
psi_minus	16,57	-0.0
psi_minus	17,57	-0.0
psi_minus	18,57	0.0
psi_minus	19,57	0.0
psi_minus	20,57	-0.0
psi_minus	1,58	-0.0
psi_minus	2,58	0.0
psi_minus	3,58	-0.0
psi_minus	4,58	0.0
psi_minus	5,58	0.0
psi_minus	6,58	0.0
psi_minus	7,58	0.0
psi_minus	8,58	-0.0
psi_minus	9,58	-0.0
psi_minus	10,58	-0.0
psi_minus	11,58	0.0
psi_minus	12,58	0.0
psi_minus	13,58	0.0
psi_minus	14,58	-0.0
psi_minus	15,58	0.0
psi_minus	16,58	-0.0
psi_minus	17,58	-0.0
psi_minus	18,58	0.0
psi_minus	19,58	0.0
psi_minus	20,58	-0.0
psi_minus	1,59	-0.0
psi_minus	2,59	0.0
psi_minus	3,59	-0.0
psi_minus	4,59	0.0
psi_minus	5,59	0.0
psi_minus	6,59	0.0
psi_minus	7,59	0.0
psi_minus	8,59	-0.0
psi_minus	9,59	-0.0
psi_minus	10,59	-0.0
psi_minus	11,59	0.0
psi_minus	12,59	0.0
psi_minus	13,59	0.0
psi_minus	14,59	-0.0
psi_minus	15,59	0.0
psi_minus	16,59	-0.0
psi_minus	17,59	-0.0
psi_minus	18,59	0.0
psi_minus	19,59	0.0
psi_minus	20,59	-0.0
psi_minus	1,60	-0.0
psi_minus	2,60	0.0
psi_minus	3,60	-0.0
psi_minus	4,60	0.0
psi_minus	5,60	0.0
psi_minus	6,60	0.0
psi_minus	7,60	0.0
psi_minus	8,60	-0.0
psi_minus	9,60	-0.0
psi_minus	10,60	-0.0
psi_minus	11,60	0.0
psi_minus	12,60	0.0
psi_minus	13,60	0.0
psi_minus	14,60	-0.0
psi_minus	15,60	0.0
psi_minus	16,60	-0.0
psi_minus	17,60	-0.0
psi_minus	18,60	0.0
psi_minus	19,60	0.0
psi_minus	20,60	-0.0
psi_minus	1,61	-0.0
psi_minus	2,61	0.0
psi_minus	3,61	-0.0
psi_minus	4,61	0.0
psi_minus	5,61	0.0
psi_minus	6,61	0.0
psi_minus	7,61	0.0
psi_minus	8,61	-0.0
psi_minus	9,61	-0.0
psi_minus	10,61	-0.0
psi_minus	11,61	0.0
psi_minus	12,61	0.0
psi_minus	13,61	0.0
psi_minus	14,61	-0.0
psi_minus	15,61	0.0
psi_minus	16,61	-0.0
psi_minus	17,61	-0.0
psi_minus	18,61	0.0
psi_minus	19,61	0.0
psi_minus	20,61	-0.0
psi_minus	1,62	-0.0
psi_minus	2,62	0.0
psi_minus	3,62	-0.0
psi_minus	4,62	0.0
psi_minus	5,62	0.0
psi_minus	6,62	0.0
psi_minus	7,62	0.0
psi_minus	8,62	-0.0
psi_minus	9,62	-0.0
psi_minus	10,62	-0.0
psi_minus	11,62	0.0
psi_minus	12,62	0.0
psi_minus	13,62	0.0
psi_minus	14,62	-0.0
psi_minus	15,62	0.0
psi_minus	16,62	-0.0
psi_minus	17,62	-0.0
psi_minus	18,62	0.0
psi_minus	19,62	0.0
psi_minus	20,62	-0.0
psi_minus	1,63	-0.0
psi_minus	2,63	0.0
psi_minus	3,63	-0.0
psi_minus	4,63	0.0
psi_minus	5,63	0.0
psi_minus	6,63	0.0
psi_minus	7,63	0.0
psi_minus	8,63	-0.0
psi_minus	9,63	-0.0
psi_minus	10,63	-0.0
psi_minus	11,63	0.0
psi_minus	12,63	0.0
psi_minus	13,63	0.0
psi_minus	14,63	-0.0
psi_minus	15,63	0.0
psi_minus	16,63	-0.0
psi_minus	17,63	-0.0
psi_minus	18,63	0.0
psi_minus	19,63	0.0
psi_minus	20,63	-0.0
psi_minus	1,64	-0.0
psi_minus	2,64	0.0
psi_minus	3,64	-0.0
psi_minus	4,64	0.0
psi_minus	5,64	0.0
psi_minus	6,64	0.0
psi_minus	7,64	0.0
psi_minus	8,64	-0.0
psi_minus	9,64	-0.0
psi_minus	10,64	-0.0
psi_minus	11,64	0.0
psi_minus	12,64	0.0
psi_minus	13,64	0.0
psi_minus	14,64	-0.0
psi_minus	15,64	0.0
psi_minus	16,64	-0.0
psi_minus	17,64	-0.0
psi_minus	18,64	0.0
psi_minus	19,64	0.0
psi_minus	20,64	-0.0
psi_minus	1,65	-0.0
psi_minus	2,65	0.0
psi_minus	3,65	-0.0
psi_minus	4,65	0.0
psi_minus	5,65	0.0
psi_minus	6,65	0.0
psi_minus	7,65	0.0
psi_minus	8,65	-0.0
psi_minus	9,65	-0.0
psi_minus	10,65	-0.0
psi_minus	11,65	0.0
psi_minus	12,65	0.0
psi_minus	13,65	0.0
psi_minus	14,65	-0.0
psi_minus	15,65	0.0
psi_minus	16,65	-0.0
psi_minus	17,65	-0.0
psi_minus	18,65	0.0
psi_minus	19,65	0.0
psi_minus	20,65	-0.0
psi_minus	1,66	-0.0
psi_minus	2,66	0.0
psi_minus	3,66	-0.0
psi_minus	4,66	0.0
psi_minus	5,66	0.0
psi_minus	6,66	0.0
psi_minus	7,66	0.0
psi_minus	8,66	-0.0
psi_minus	9,66	-0.0
psi_minus	10,66	-0.0
psi_minus	11,66	0.0
psi_minus	12,66	0.0
psi_minus	13,66	0.0
psi_minus	14,66	-0.0
psi_minus	15,66	0.0
psi_minus	16,66	-0.0
psi_minus	17,66	-0.0
psi_minus	18,66	0.0
psi_minus	19,66	0.0
psi_minus	20,66	-0.0
psi_minus	1,67	-0.0
psi_minus	2,67	0.0
psi_minus	3,67	-0.0
psi_minus	4,67	0.0
psi_minus	5,67	0.0
psi_minus	6,67	0.0
psi_minus	7,67	0.0
psi_minus	8,67	-0.0
psi_minus	9,67	-0.0
psi_minus	10,67	-0.0
psi_minus	11,67	0.0
psi_minus	12,67	0.0
psi_minus	13,67	0.0
psi_minus	14,67	-0.0
psi_minus	15,67	0.0
psi_minus	16,67	-0.0
psi_minus	17,67	-0.0
psi_minus	18,67	0.0
psi_minus	19,67	0.0
psi_minus	20,67	-0.0
psi_minus	1,68	-0.0
psi_minus	2,68	0.0
psi_minus	3,68	-0.0
psi_minus	4,68	0.0
psi_minus	5,68	0.0
psi_minus	6,68	0.0
psi_minus	7,68	0.0
psi_minus	8,68	-0.0
psi_minus	9,68	-0.0
psi_minus	10,68	-0.0
psi_minus	11,68	0.0
psi_minus	12,68	0.0
psi_minus	13,68	0.0
psi_minus	14,68	-0.0
psi_minus	15,68	0.0
psi_minus	16,68	-0.0
psi_minus	17,68	-0.0
psi_minus	18,68	0.0
psi_minus	19,68	0.0
psi_minus	20,68	-0.0
psi_minus	1,69	0.0
psi_minus	2,69	0.0
psi_minus	3,69	0.0
psi_minus	4,69	0.0
psi_minus	5,69	0.0
psi_minus	6,69	0.0
psi_minus	7,69	0.0
psi_minus	8,69	0.0
psi_minus	9,69	0.0
psi_minus	10,69	0.0
psi_minus	11,69	0.0
psi_minus	12,69	0.0
psi_minus	13,69	0.0
psi_minus	14,69	0.0
psi_minus	15,69	0.0
psi_minus	16,69	0.0
psi_minus	17,69	0.0
psi_minus	18,69	0.0
psi_minus	19,69	0.0
psi_minus	20,69	0.0
psi_minus	1,70	0.0
psi_minus	2,70	0.0
psi_minus	3,70	0.0
psi_minus	4,70	0.0
psi_minus	5,70	0.0
psi_minus	6,70	0.0
psi_minus	7,70	0.0
psi_minus	8,70	0.0
psi_minus	9,70	0.0
psi_minus	10,70	0.0
psi_minus	11,70	0.0
psi_minus	12,70	0.0
psi_minus	13,70	0.0
psi_minus	14,70	0.0
psi_minus	15,70	0.0
psi_minus	16,70	0.0
psi_minus	17,70	0.0
psi_minus	18,70	0.0
psi_minus	19,70	0.0
psi_minus	20,70	0.0
psi_minus	1,71	0.0
psi_minus	2,71	0.0
psi_minus	3,71	0.0
psi_minus	4,71	0.0
psi_minus	5,71	0.0
psi_minus	6,71	0.0
psi_minus	7,71	0.0
psi_minus	8,71	0.0
psi_minus	9,71	0.0
psi_minus	10,71	0.0
psi_minus	11,71	0.0
psi_minus	12,71	0.0
psi_minus	13,71	0.0
psi_minus	14,71	0.0
psi_minus	15,71	0.0
psi_minus	16,71	0.0
psi_minus	17,71	0.0
psi_minus	18,71	0.0
psi_minus	19,71	0.0
psi_minus	20,71	0.0
psi_minus	1,72	0.0
psi_minus	2,72	0.0
psi_minus	3,72	0.0
psi_minus	4,72	0.0
psi_minus	5,72	0.0
psi_minus	6,72	0.0
psi_minus	7,72	0.0
psi_minus	8,72	0.0
psi_minus	9,72	0.0
psi_minus	10,72	0.0
psi_minus	11,72	0.0
psi_minus	12,72	0.0
psi_minus	13,72	0.0
psi_minus	14,72	0.0
psi_minus	15,72	0.0
psi_minus	16,72	0.0
psi_minus	17,72	0.0
psi_minus	18,72	0.0
psi_minus	19,72	0.0
psi_minus	20,72	0.0
psi_minus	1,73	0.0
psi_minus	2,73	0.0
psi_minus	3,73	0.0
psi_minus	4,73	0.0
psi_minus	5,73	0.0
psi_minus	6,73	0.0
psi_minus	7,73	0.0
psi_minus	8,73	0.0
psi_minus	9,73	0.0
psi_minus	10,73	0.0
psi_minus	11,73	0.0
psi_minus	12,73	0.0
psi_minus	13,73	0.0
psi_minus	14,73	0.0
psi_minus	15,73	0.0
psi_minus	16,73	0.0
psi_minus	17,73	0.0
psi_minus	18,73	0.0
psi_minus	19,73	0.0
psi_minus	20,73	0.0
psi_minus	1,74	0.0
psi_minus	2,74	0.0
psi_minus	3,74	0.0
psi_minus	4,74	0.0
psi_minus	5,74	0.0
psi_minus	6,74	0.0
psi_minus	7,74	0.0
psi_minus	8,74	0.0
psi_minus	9,74	0.0
psi_minus	10,74	0.0
psi_minus	11,74	0.0
psi_minus	12,74	0.0
psi_minus	13,74	0.0
psi_minus	14,74	0.0
psi_minus	15,74	0.0
psi_minus	16,74	0.0
psi_minus	17,74	0.0
psi_minus	18,74	0.0
psi_minus	19,74	0.0
psi_minus	20,74	0.0
psi_minus	1,75	0.0
psi_minus	2,75	0.0
psi_minus	3,75	0.0
psi_minus	4,75	0.0
psi_minus	5,75	0.0
psi_minus	6,75	0.0
psi_minus	7,75	0.0
psi_minus	8,75	0.0
psi_minus	9,75	0.0
psi_minus	10,75	0.0
psi_minus	11,75	0.0
psi_minus	12,75	0.0
psi_minus	13,75	0.0
psi_minus	14,75	0.0
psi_minus	15,75	0.0
psi_minus	16,75	0.0
psi_minus	17,75	0.0
psi_minus	18,75	0.0
psi_minus	19,75	0.0
psi_minus	20,75	0.0
psi_minus	1,76	0.0
psi_minus	2,76	0.0
psi_minus	3,76	0.0
psi_minus	4,76	0.0
psi_minus	5,76	0.0
psi_minus	6,76	0.0
psi_minus	7,76	0.0
psi_minus	8,76	0.0
psi_minus	9,76	0.0
psi_minus	10,76	0.0
psi_minus	11,76	0.0
psi_minus	12,76	0.0
psi_minus	13,76	0.0
psi_minus	14,76	0.0
psi_minus	15,76	0.0
psi_minus	16,76	0.0
psi_minus	17,76	0.0
psi_minus	18,76	0.0
psi_minus	19,76	0.0
psi_minus	20,76	0.0
psi_minus	1,77	0.0
psi_minus	2,77	0.0
psi_minus	3,77	0.0
psi_minus	4,77	0.0
psi_minus	5,77	0.0
psi_minus	6,77	0.0
psi_minus	7,77	0.0
psi_minus	8,77	0.0
psi_minus	9,77	0.0
psi_minus	10,77	0.0
psi_minus	11,77	0.0
psi_minus	12,77	0.0
psi_minus	13,77	0.0
psi_minus	14,77	0.0
psi_minus	15,77	0.0
psi_minus	16,77	0.0
psi_minus	17,77	0.0
psi_minus	18,77	0.0
psi_minus	19,77	0.0
psi_minus	20,77	0.0
psi_minus	1,78	0.0
psi_minus	2,78	0.0
psi_minus	3,78	0.0
psi_minus	4,78	0.0
psi_minus	5,78	0.0
psi_minus	6,78	0.0
psi_minus	7,78	0.0
psi_minus	8,78	0.0
psi_minus	9,78	0.0
psi_minus	10,78	0.0
psi_minus	11,78	0.0
psi_minus	12,78	0.0
psi_minus	13,78	0.0
psi_minus	14,78	0.0
psi_minus	15,78	0.0
psi_minus	16,78	0.0
psi_minus	17,78	0.0
psi_minus	18,78	0.0
psi_minus	19,78	0.0
psi_minus	20,78	0.0
psi_minus	1,79	-0.0
psi_minus	2,79	0.0
psi_minus	3,79	-0.0
psi_minus	4,79	0.0
psi_minus	5,79	0.0
psi_minus	6,79	0.0
psi_minus	7,79	0.0
psi_minus	8,79	-0.0
psi_minus	9,79	-0.0
psi_minus	10,79	-0.0
psi_minus	11,79	0.0
psi_minus	12,79	0.0
psi_minus	13,79	0.0
psi_minus	14,79	-0.0
psi_minus	15,79	0.0
psi_minus	16,79	-0.0
psi_minus	17,79	-0.0
psi_minus	18,79	0.0
psi_minus	19,79	0.0
psi_minus	20,79	-0.0
psi_minus	1,80	-0.0
psi_minus	2,80	0.0
psi_minus	3,80	-0.0
psi_minus	4,80	0.0
psi_minus	5,80	0.0
psi_minus	6,80	0.0
psi_minus	7,80	0.0
psi_minus	8,80	-0.0
psi_minus	9,80	-0.0
psi_minus	10,80	-0.0
psi_minus	11,80	0.0
psi_minus	12,80	0.0
psi_minus	13,80	0.0
psi_minus	14,80	-0.0
psi_minus	15,80	0.0
psi_minus	16,80	-0.0
psi_minus	17,80	-0.0
psi_minus	18,80	0.0
psi_minus	19,80	0.0
psi_minus	20,80	-0.0
psi_minus	1,81	-0.0
psi_minus	2,81	0.0
psi_minus	3,81	-0.0
psi_minus	4,81	0.0
psi_minus	5,81	0.0
psi_minus	6,81	0.0
psi_minus	7,81	0.0
psi_minus	8,81	-0.0
psi_minus	9,81	-0.0
psi_minus	10,81	-0.0
psi_minus	11,81	0.0
psi_minus	12,81	0.0
psi_minus	13,81	0.0
psi_minus	14,81	-0.0
psi_minus	15,81	0.0
psi_minus	16,81	-0.0
psi_minus	17,81	-0.0
psi_minus	18,81	0.0
psi_minus	19,81	0.0
psi_minus	20,81	-0.0
psi_minus	1,82	-0.0
psi_minus	2,82	0.0
psi_minus	3,82	-0.0
psi_minus	4,82	0.0
psi_minus	5,82	0.0
psi_minus	6,82	0.0
psi_minus	7,82	0.0
psi_minus	8,82	-0.0
psi_minus	9,82	-0.0
psi_minus	10,82	-0.0
psi_minus	11,82	0.0
psi_minus	12,82	0.0
psi_minus	13,82	0.0
psi_minus	14,82	-0.0
psi_minus	15,82	0.0
psi_minus	16,82	-0.0
psi_minus	17,82	-0.0
psi_minus	18,82	0.0
psi_minus	19,82	0.0
psi_minus	20,82	-0.0
psi_minus	1,83	-0.0
psi_minus	2,83	0.0
psi_minus	3,83	-0.0
psi_minus	4,83	0.0
psi_minus	5,83	0.0
psi_minus	6,83	0.0
psi_minus	7,83	0.0
psi_minus	8,83	-0.0
psi_minus	9,83	-0.0
psi_minus	10,83	-0.0
psi_minus	11,83	0.0
psi_minus	12,83	0.0
psi_minus	13,83	0.0
psi_minus	14,83	-0.0
psi_minus	15,83	0.0
psi_minus	16,83	-0.0
psi_minus	17,83	-0.0
psi_minus	18,83	0.0
psi_minus	19,83	0.0
psi_minus	20,83	-0.0
psi_minus	1,84	-0.0
psi_minus	2,84	0.0
psi_minus	3,84	-0.0
psi_minus	4,84	0.0
psi_minus	5,84	0.0
psi_minus	6,84	0.0
psi_minus	7,84	0.0
psi_minus	8,84	-0.0
psi_minus	9,84	-0.0
psi_minus	10,84	-0.0
psi_minus	11,84	0.0
psi_minus	12,84	0.0
psi_minus	13,84	0.0
psi_minus	14,84	-0.0
psi_minus	15,84	0.0
psi_minus	16,84	-0.0
psi_minus	17,84	-0.0
psi_minus	18,84	0.0
psi_minus	19,84	0.0
psi_minus	20,84	-0.0
psi_minus	1,85	-0.0
psi_minus	2,85	0.0
psi_minus	3,85	-0.0
psi_minus	4,85	0.0
psi_minus	5,85	0.0
psi_minus	6,85	0.0
psi_minus	7,85	0.0
psi_minus	8,85	-0.0
psi_minus	9,85	-0.0
psi_minus	10,85	-0.0
psi_minus	11,85	0.0
psi_minus	12,85	0.0
psi_minus	13,85	0.0
psi_minus	14,85	-0.0
psi_minus	15,85	0.0
psi_minus	16,85	-0.0
psi_minus	17,85	-0.0
psi_minus	18,85	0.0
psi_minus	19,85	0.0
psi_minus	20,85	-0.0
psi_minus	1,86	-0.0
psi_minus	2,86	0.0
psi_minus	3,86	-0.0
psi_minus	4,86	0.0
psi_minus	5,86	0.0
psi_minus	6,86	0.0
psi_minus	7,86	0.0
psi_minus	8,86	-0.0
psi_minus	9,86	-0.0
psi_minus	10,86	-0.0
psi_minus	11,86	0.0
psi_minus	12,86	0.0
psi_minus	13,86	0.0
psi_minus	14,86	-0.0
psi_minus	15,86	0.0
psi_minus	16,86	-0.0
psi_minus	17,86	-0.0
psi_minus	18,86	0.0
psi_minus	19,86	0.0
psi_minus	20,86	-0.0
psi_minus	1,87	-0.0
psi_minus	2,87	0.0
psi_minus	3,87	-0.0
psi_minus	4,87	0.0
psi_minus	5,87	0.0
psi_minus	6,87	0.0
psi_minus	7,87	0.0
psi_minus	8,87	-0.0
psi_minus	9,87	-0.0
psi_minus	10,87	-0.0
psi_minus	11,87	0.0
psi_minus	12,87	0.0
psi_minus	13,87	0.0
psi_minus	14,87	-0.0
psi_minus	15,87	0.0
psi_minus	16,87	-0.0
psi_minus	17,87	-0.0
psi_minus	18,87	0.0
psi_minus	19,87	0.0
psi_minus	20,87	-0.0
psi_minus	1,88	-0.0
psi_minus	2,88	0.0
psi_minus	3,88	-0.0
psi_minus	4,88	0.0
psi_minus	5,88	0.0
psi_minus	6,88	0.0
psi_minus	7,88	0.0
psi_minus	8,88	-0.0
psi_minus	9,88	-0.0
psi_minus	10,88	-0.0
psi_minus	11,88	0.0
psi_minus	12,88	0.0
psi_minus	13,88	0.0
psi_minus	14,88	-0.0
psi_minus	15,88	0.0
psi_minus	16,88	-0.0
psi_minus	17,88	-0.0
psi_minus	18,88	0.0
psi_minus	19,88	0.0
psi_minus	20,88	-0.0
psi_minus	1,89	-0.0
psi_minus	2,89	0.0
psi_minus	3,89	-0.0
psi_minus	4,89	0.0
psi_minus	5,89	0.0
psi_minus	6,89	0.0
psi_minus	7,89	0.0
psi_minus	8,89	-0.0
psi_minus	9,89	-0.0
psi_minus	10,89	-0.0
psi_minus	11,89	0.0
psi_minus	12,89	0.0
psi_minus	13,89	0.0
psi_minus	14,89	-0.0
psi_minus	15,89	0.0
psi_minus	16,89	-0.0
psi_minus	17,89	-0.0
psi_minus	18,89	0.0
psi_minus	19,89	0.0
psi_minus	20,89	-0.0
psi_minus	1,90	-0.0
psi_minus	2,90	0.0
psi_minus	3,90	-0.0
psi_minus	4,90	0.0
psi_minus	5,90	0.0
psi_minus	6,90	0.0
psi_minus	7,90	0.0
psi_minus	8,90	-0.0
psi_minus	9,90	-0.0
psi_minus	10,90	-0.0
psi_minus	11,90	0.0
psi_minus	12,90	0.0
psi_minus	13,90	0.0
psi_minus	14,90	-0.0
psi_minus	15,90	0.0
psi_minus	16,90	-0.0
psi_minus	17,90	-0.0
psi_minus	18,90	0.0
psi_minus	19,90	0.0
psi_minus	20,90	-0.0
psi_minus	1,91	-0.0
psi_minus	2,91	0.0
psi_minus	3,91	-0.0
psi_minus	4,91	0.0
psi_minus	5,91	0.0
psi_minus	6,91	0.0
psi_minus	7,91	0.0
psi_minus	8,91	-0.0
psi_minus	9,91	-0.0
psi_minus	10,91	-0.0
psi_minus	11,91	0.0
psi_minus	12,91	0.0
psi_minus	13,91	0.0
psi_minus	14,91	-0.0
psi_minus	15,91	0.0
psi_minus	16,91	-0.0
psi_minus	17,91	-0.0
psi_minus	18,91	0.0
psi_minus	19,91	0.0
psi_minus	20,91	-0.0
psi_minus	1,92	-0.0
psi_minus	2,92	0.0
psi_minus	3,92	-0.0
psi_minus	4,92	0.0
psi_minus	5,92	0.0
psi_minus	6,92	0.0
psi_minus	7,92	0.0
psi_minus	8,92	-0.0
psi_minus	9,92	-0.0
psi_minus	10,92	-0.0
psi_minus	11,92	0.0
psi_minus	12,92	0.0
psi_minus	13,92	0.0
psi_minus	14,92	-0.0
psi_minus	15,92	0.0
psi_minus	16,92	-0.0
psi_minus	17,92	-0.0
psi_minus	18,92	0.0
psi_minus	19,92	0.0
psi_minus	20,92	-0.0
psi_minus	1,93	0.0
psi_minus	2,93	0.0
psi_minus	3,93	0.0
psi_minus	4,93	0.0
psi_minus	5,93	0.0
psi_minus	6,93	0.0
psi_minus	7,93	0.0
psi_minus	8,93	0.0
psi_minus	9,93	0.0
psi_minus	10,93	0.0
psi_minus	11,93	0.0
psi_minus	12,93	0.0
psi_minus	13,93	0.0
psi_minus	14,93	0.0
psi_minus	15,93	0.0
psi_minus	16,93	0.0
psi_minus	17,93	0.0
psi_minus	18,93	0.0
psi_minus	19,93	0.0
psi_minus	20,93	0.0
psi_minus	1,94	0.0
psi_minus	2,94	0.0
psi_minus	3,94	0.0
psi_minus	4,94	0.0
psi_minus	5,94	0.0
psi_minus	6,94	0.0
psi_minus	7,94	0.0
psi_minus	8,94	0.0
psi_minus	9,94	0.0
psi_minus	10,94	0.0
psi_minus	11,94	0.0
psi_minus	12,94	0.0
psi_minus	13,94	0.0
psi_minus	14,94	0.0
psi_minus	15,94	0.0
psi_minus	16,94	0.0
psi_minus	17,94	0.0
psi_minus	18,94	0.0
psi_minus	19,94	0.0
psi_minus	20,94	0.0
psi_minus	1,95	0.0
psi_minus	2,95	0.0
psi_minus	3,95	0.0
psi_minus	4,95	0.0
psi_minus	5,95	0.0
psi_minus	6,95	0.0
psi_minus	7,95	0.0
psi_minus	8,95	0.0
psi_minus	9,95	0.0
psi_minus	10,95	0.0
psi_minus	11,95	0.0
psi_minus	12,95	0.0
psi_minus	13,95	0.0
psi_minus	14,95	0.0
psi_minus	15,95	0.0
psi_minus	16,95	0.0
psi_minus	17,95	0.0
psi_minus	18,95	0.0
psi_minus	19,95	0.0
psi_minus	20,95	0.0
psi_minus	1,96	0.0
psi_minus	2,96	0.0
psi_minus	3,96	0.0
psi_minus	4,96	0.0
psi_minus	5,96	0.0
psi_minus	6,96	0.0
psi_minus	7,96	0.0
psi_minus	8,96	0.0
psi_minus	9,96	0.0
psi_minus	10,96	0.0
psi_minus	11,96	0.0
psi_minus	12,96	0.0
psi_minus	13,96	0.0
psi_minus	14,96	0.0
psi_minus	15,96	0.0
psi_minus	16,96	0.0
psi_minus	17,96	0.0
psi_minus	18,96	0.0
psi_minus	19,96	0.0
psi_minus	20,96	0.0
psi_plus	1,1	0.0
psi_plus	2,1	0.0
psi_plus	3,1	0.0
psi_plus	4,1	0.0
psi_plus	5,1	0.0
psi_plus	6,1	0.0
psi_plus	7,1	0.0
psi_plus	8,1	0.0
psi_plus	9,1	0.0
psi_plus	10,1	0.0
psi_plus	11,1	0.0
psi_plus	12,1	0.0
psi_plus	13,1	0.0
psi_plus	14,1	0.0
psi_plus	15,1	0.0
psi_plus	16,1	0.0
psi_plus	17,1	0.0
psi_plus	18,1	0.0
psi_plus	19,1	0.0
psi_plus	20,1	0.0
psi_plus	1,2	0.0
psi_plus	2,2	0.0
psi_plus	3,2	0.0
psi_plus	4,2	0.0
psi_plus	5,2	0.0
psi_plus	6,2	0.0
psi_plus	7,2	0.0
psi_plus	8,2	0.0
psi_plus	9,2	0.0
psi_plus	10,2	0.0
psi_plus	11,2	0.0
psi_plus	12,2	0.0
psi_plus	13,2	0.0
psi_plus	14,2	0.0
psi_plus	15,2	0.0
psi_plus	16,2	0.0
psi_plus	17,2	0.0
psi_plus	18,2	0.0
psi_plus	19,2	0.0
psi_plus	20,2	0.0
psi_plus	1,3	0.0
psi_plus	2,3	0.0
psi_plus	3,3	0.0
psi_plus	4,3	0.0
psi_plus	5,3	0.0
psi_plus	6,3	0.0
psi_plus	7,3	0.0
psi_plus	8,3	0.0
psi_plus	9,3	0.0
psi_plus	10,3	0.0
psi_plus	11,3	0.0
psi_plus	12,3	0.0
psi_plus	13,3	0.0
psi_plus	14,3	0.0
psi_plus	15,3	0.0
psi_plus	16,3	0.0
psi_plus	17,3	0.0
psi_plus	18,3	0.0
psi_plus	19,3	0.0
psi_plus	20,3	0.0
psi_plus	1,4	0.0
psi_plus	2,4	0.0
psi_plus	3,4	0.0
psi_plus	4,4	0.0
psi_plus	5,4	0.0
psi_plus	6,4	0.0
psi_plus	7,4	0.0
psi_plus	8,4	0.0
psi_plus	9,4	0.0
psi_plus	10,4	0.0
psi_plus	11,4	0.0
psi_plus	12,4	0.0
psi_plus	13,4	0.0
psi_plus	14,4	0.0
psi_plus	15,4	0.0
psi_plus	16,4	0.0
psi_plus	17,4	0.0
psi_plus	18,4	0.0
psi_plus	19,4	0.0
psi_plus	20,4	0.0
psi_plus	1,5	0.0
psi_plus	2,5	0.0
psi_plus	3,5	0.0
psi_plus	4,5	0.0
psi_plus	5,5	0.0
psi_plus	6,5	0.0
psi_plus	7,5	0.0
psi_plus	8,5	0.0
psi_plus	9,5	0.0
psi_plus	10,5	0.0
psi_plus	11,5	0.0
psi_plus	12,5	0.0
psi_plus	13,5	0.0
psi_plus	14,5	0.0
psi_plus	15,5	0.0
psi_plus	16,5	0.0
psi_plus	17,5	0.0
psi_plus	18,5	0.0
psi_plus	19,5	0.0
psi_plus	20,5	0.0
psi_plus	1,6	0.0
psi_plus	2,6	0.0
psi_plus	3,6	0.0
psi_plus	4,6	0.0
psi_plus	5,6	0.0
psi_plus	6,6	0.0
psi_plus	7,6	0.0
psi_plus	8,6	0.0
psi_plus	9,6	0.0
psi_plus	10,6	0.0
psi_plus	11,6	0.0
psi_plus	12,6	0.0
psi_plus	13,6	0.0
psi_plus	14,6	0.0
psi_plus	15,6	0.0
psi_plus	16,6	0.0
psi_plus	17,6	0.0
psi_plus	18,6	0.0
psi_plus	19,6	0.0
psi_plus	20,6	0.0
psi_plus	1,7	1.0
psi_plus	2,7	1.0
psi_plus	3,7	1.0
psi_plus	4,7	1.0
psi_plus	5,7	1.0
psi_plus	6,7	1.0
psi_plus	7,7	1.0
psi_plus	8,7	1.0
psi_plus	9,7	1.0
psi_plus	10,7	1.0
psi_plus	11,7	1.0
psi_plus	12,7	1.0
psi_plus	13,7	1.0
psi_plus	14,7	1.0
psi_plus	15,7	1.0
psi_plus	16,7	1.0
psi_plus	17,7	1.0
psi_plus	18,7	1.0
psi_plus	19,7	1.0
psi_plus	20,7	1.0
psi_plus	1,8	1.0
psi_plus	2,8	1.0
psi_plus	3,8	1.0
psi_plus	4,8	1.0
psi_plus	5,8	1.0
psi_plus	6,8	1.0
psi_plus	7,8	1.0
psi_plus	8,8	1.0
psi_plus	9,8	1.0
psi_plus	10,8	1.0
psi_plus	11,8	1.0
psi_plus	12,8	1.0
psi_plus	13,8	1.0
psi_plus	14,8	1.0
psi_plus	15,8	1.0
psi_plus	16,8	1.0
psi_plus	17,8	1.0
psi_plus	18,8	1.0
psi_plus	19,8	1.0
psi_plus	20,8	1.0
psi_plus	1,9	1.0
psi_plus	2,9	1.0
psi_plus	3,9	1.0
psi_plus	4,9	1.0
psi_plus	5,9	1.0
psi_plus	6,9	1.0
psi_plus	7,9	1.0
psi_plus	8,9	1.0
psi_plus	9,9	1.0
psi_plus	10,9	1.0
psi_plus	11,9	1.0
psi_plus	12,9	1.0
psi_plus	13,9	1.0
psi_plus	14,9	1.0
psi_plus	15,9	1.0
psi_plus	16,9	1.0
psi_plus	17,9	1.0
psi_plus	18,9	1.0
psi_plus	19,9	1.0
psi_plus	20,9	1.0
psi_plus	1,10	1.0
psi_plus	2,10	1.0
psi_plus	3,10	1.0
psi_plus	4,10	1.0
psi_plus	5,10	1.0
psi_plus	6,10	1.0
psi_plus	7,10	1.0
psi_plus	8,10	1.0
psi_plus	9,10	1.0
psi_plus	10,10	1.0
psi_plus	11,10	1.0
psi_plus	12,10	1.0
psi_plus	13,10	1.0
psi_plus	14,10	1.0
psi_plus	15,10	1.0
psi_plus	16,10	1.0
psi_plus	17,10	1.0
psi_plus	18,10	1.0
psi_plus	19,10	1.0
psi_plus	20,10	1.0
psi_plus	1,11	1.0
psi_plus	2,11	1.0
psi_plus	3,11	1.0
psi_plus	4,11	1.0
psi_plus	5,11	1.0
psi_plus	6,11	1.0
psi_plus	7,11	1.0
psi_plus	8,11	1.0
psi_plus	9,11	1.0
psi_plus	10,11	1.0
psi_plus	11,11	1.0
psi_plus	12,11	1.0
psi_plus	13,11	1.0
psi_plus	14,11	1.0
psi_plus	15,11	1.0
psi_plus	16,11	1.0
psi_plus	17,11	1.0
psi_plus	18,11	1.0
psi_plus	19,11	1.0
psi_plus	20,11	1.0
psi_plus	1,12	1.0
psi_plus	2,12	1.0
psi_plus	3,12	1.0
psi_plus	4,12	1.0
psi_plus	5,12	1.0
psi_plus	6,12	1.0
psi_plus	7,12	1.0
psi_plus	8,12	1.0
psi_plus	9,12	1.0
psi_plus	10,12	1.0
psi_plus	11,12	1.0
psi_plus	12,12	1.0
psi_plus	13,12	1.0
psi_plus	14,12	1.0
psi_plus	15,12	1.0
psi_plus	16,12	1.0
psi_plus	17,12	1.0
psi_plus	18,12	1.0
psi_plus	19,12	1.0
psi_plus	20,12	1.0
psi_plus	1,13	1.0
psi_plus	2,13	1.0
psi_plus	3,13	1.0
psi_plus	4,13	1.0
psi_plus	5,13	1.0
psi_plus	6,13	1.0
psi_plus	7,13	1.0
psi_plus	8,13	1.0
psi_plus	9,13	1.0
psi_plus	10,13	1.0
psi_plus	11,13	1.0
psi_plus	12,13	1.0
psi_plus	13,13	1.0
psi_plus	14,13	1.0
psi_plus	15,13	1.0
psi_plus	16,13	1.0
psi_plus	17,13	1.0
psi_plus	18,13	1.0
psi_plus	19,13	1.0
psi_plus	20,13	1.0
psi_plus	1,14	1.0
psi_plus	2,14	1.0
psi_plus	3,14	1.0
psi_plus	4,14	1.0
psi_plus	5,14	1.0
psi_plus	6,14	1.0
psi_plus	7,14	1.0
psi_plus	8,14	1.0
psi_plus	9,14	1.0
psi_plus	10,14	1.0
psi_plus	11,14	1.0
psi_plus	12,14	1.0
psi_plus	13,14	1.0
psi_plus	14,14	1.0
psi_plus	15,14	1.0
psi_plus	16,14	1.0
psi_plus	17,14	1.0
psi_plus	18,14	1.0
psi_plus	19,14	1.0
psi_plus	20,14	1.0
psi_plus	1,15	1.0
psi_plus	2,15	1.0
psi_plus	3,15	1.0
psi_plus	4,15	1.0
psi_plus	5,15	1.0
psi_plus	6,15	1.0
psi_plus	7,15	1.0
psi_plus	8,15	1.0
psi_plus	9,15	1.0
psi_plus	10,15	1.0
psi_plus	11,15	1.0
psi_plus	12,15	1.0
psi_plus	13,15	1.0
psi_plus	14,15	1.0
psi_plus	15,15	1.0
psi_plus	16,15	1.0
psi_plus	17,15	1.0
psi_plus	18,15	1.0
psi_plus	19,15	1.0
psi_plus	20,15	1.0
psi_plus	1,16	1.0
psi_plus	2,16	1.0
psi_plus	3,16	1.0
psi_plus	4,16	1.0
psi_plus	5,16	1.0
psi_plus	6,16	1.0
psi_plus	7,16	1.0
psi_plus	8,16	1.0
psi_plus	9,16	1.0
psi_plus	10,16	1.0
psi_plus	11,16	1.0
psi_plus	12,16	1.0
psi_plus	13,16	1.0
psi_plus	14,16	1.0
psi_plus	15,16	1.0
psi_plus	16,16	1.0
psi_plus	17,16	1.0
psi_plus	18,16	1.0
psi_plus	19,16	1.0
psi_plus	20,16	1.0
psi_plus	1,17	1.0
psi_plus	2,17	1.0
psi_plus	3,17	1.0
psi_plus	4,17	1.0
psi_plus	5,17	1.0
psi_plus	6,17	1.0
psi_plus	7,17	1.0
psi_plus	8,17	1.0
psi_plus	9,17	1.0
psi_plus	10,17	1.0
psi_plus	11,17	1.0
psi_plus	12,17	1.0
psi_plus	13,17	1.0
psi_plus	14,17	1.0
psi_plus	15,17	1.0
psi_plus	16,17	1.0
psi_plus	17,17	1.0
psi_plus	18,17	1.0
psi_plus	19,17	1.0
psi_plus	20,17	1.0
psi_plus	1,18	1.0
psi_plus	2,18	1.0
psi_plus	3,18	1.0
psi_plus	4,18	1.0
psi_plus	5,18	1.0
psi_plus	6,18	1.0
psi_plus	7,18	1.0
psi_plus	8,18	1.0
psi_plus	9,18	1.0
psi_plus	10,18	1.0
psi_plus	11,18	1.0
psi_plus	12,18	1.0
psi_plus	13,18	1.0
psi_plus	14,18	1.0
psi_plus	15,18	1.0
psi_plus	16,18	1.0
psi_plus	17,18	1.0
psi_plus	18,18	1.0
psi_plus	19,18	1.0
psi_plus	20,18	1.0
psi_plus	1,19	1.0
psi_plus	2,19	1.0
psi_plus	3,19	1.0
psi_plus	4,19	1.0
psi_plus	5,19	1.0
psi_plus	6,19	1.0
psi_plus	7,19	1.0
psi_plus	8,19	1.0
psi_plus	9,19	1.0
psi_plus	10,19	1.0
psi_plus	11,19	1.0
psi_plus	12,19	1.0
psi_plus	13,19	1.0
psi_plus	14,19	1.0
psi_plus	15,19	1.0
psi_plus	16,19	1.0
psi_plus	17,19	1.0
psi_plus	18,19	1.0
psi_plus	19,19	1.0
psi_plus	20,19	1.0
psi_plus	1,20	1.0
psi_plus	2,20	1.0
psi_plus	3,20	1.0
psi_plus	4,20	1.0
psi_plus	5,20	1.0
psi_plus	6,20	1.0
psi_plus	7,20	1.0
psi_plus	8,20	1.0
psi_plus	9,20	1.0
psi_plus	10,20	1.0
psi_plus	11,20	1.0
psi_plus	12,20	1.0
psi_plus	13,20	1.0
psi_plus	14,20	1.0
psi_plus	15,20	1.0
psi_plus	16,20	1.0
psi_plus	17,20	1.0
psi_plus	18,20	1.0
psi_plus	19,20	1.0
psi_plus	20,20	1.0
psi_plus	1,21	0.0
psi_plus	2,21	0.0
psi_plus	3,21	0.0
psi_plus	4,21	0.0
psi_plus	5,21	0.0
psi_plus	6,21	0.0
psi_plus	7,21	0.0
psi_plus	8,21	0.0
psi_plus	9,21	0.0
psi_plus	10,21	0.0
psi_plus	11,21	0.0
psi_plus	12,21	0.0
psi_plus	13,21	0.0
psi_plus	14,21	0.0
psi_plus	15,21	0.0
psi_plus	16,21	0.0
psi_plus	17,21	0.0
psi_plus	18,21	0.0
psi_plus	19,21	0.0
psi_plus	20,21	0.0
psi_plus	1,22	0.0
psi_plus	2,22	0.0
psi_plus	3,22	0.0
psi_plus	4,22	0.0
psi_plus	5,22	0.0
psi_plus	6,22	0.0
psi_plus	7,22	0.0
psi_plus	8,22	0.0
psi_plus	9,22	0.0
psi_plus	10,22	0.0
psi_plus	11,22	0.0
psi_plus	12,22	0.0
psi_plus	13,22	0.0
psi_plus	14,22	0.0
psi_plus	15,22	0.0
psi_plus	16,22	0.0
psi_plus	17,22	0.0
psi_plus	18,22	0.0
psi_plus	19,22	0.0
psi_plus	20,22	0.0
psi_plus	1,23	0.0
psi_plus	2,23	0.0
psi_plus	3,23	0.0
psi_plus	4,23	0.0
psi_plus	5,23	0.0
psi_plus	6,23	0.0
psi_plus	7,23	0.0
psi_plus	8,23	0.0
psi_plus	9,23	0.0
psi_plus	10,23	0.0
psi_plus	11,23	0.0
psi_plus	12,23	0.0
psi_plus	13,23	0.0
psi_plus	14,23	0.0
psi_plus	15,23	0.0
psi_plus	16,23	0.0
psi_plus	17,23	0.0
psi_plus	18,23	0.0
psi_plus	19,23	0.0
psi_plus	20,23	0.0
psi_plus	1,24	0.0
psi_plus	2,24	0.0
psi_plus	3,24	0.0
psi_plus	4,24	0.0
psi_plus	5,24	0.0
psi_plus	6,24	0.0
psi_plus	7,24	0.0
psi_plus	8,24	0.0
psi_plus	9,24	0.0
psi_plus	10,24	0.0
psi_plus	11,24	0.0
psi_plus	12,24	0.0
psi_plus	13,24	0.0
psi_plus	14,24	0.0
psi_plus	15,24	0.0
psi_plus	16,24	0.0
psi_plus	17,24	0.0
psi_plus	18,24	0.0
psi_plus	19,24	0.0
psi_plus	20,24	0.0
psi_plus	1,25	0.0
psi_plus	2,25	0.0
psi_plus	3,25	0.0
psi_plus	4,25	0.0
psi_plus	5,25	0.0
psi_plus	6,25	0.0
psi_plus	7,25	0.0
psi_plus	8,25	0.0
psi_plus	9,25	0.0
psi_plus	10,25	0.0
psi_plus	11,25	0.0
psi_plus	12,25	0.0
psi_plus	13,25	0.0
psi_plus	14,25	0.0
psi_plus	15,25	0.0
psi_plus	16,25	0.0
psi_plus	17,25	0.0
psi_plus	18,25	0.0
psi_plus	19,25	0.0
psi_plus	20,25	0.0
psi_plus	1,26	0.0
psi_plus	2,26	0.0
psi_plus	3,26	0.0
psi_plus	4,26	0.0
psi_plus	5,26	0.0
psi_plus	6,26	0.0
psi_plus	7,26	0.0
psi_plus	8,26	0.0
psi_plus	9,26	0.0
psi_plus	10,26	0.0
psi_plus	11,26	0.0
psi_plus	12,26	0.0
psi_plus	13,26	0.0
psi_plus	14,26	0.0
psi_plus	15,26	0.0
psi_plus	16,26	0.0
psi_plus	17,26	0.0
psi_plus	18,26	0.0
psi_plus	19,26	0.0
psi_plus	20,26	0.0
psi_plus	1,27	0.0
psi_plus	2,27	0.0
psi_plus	3,27	0.0
psi_plus	4,27	0.0
psi_plus	5,27	0.0
psi_plus	6,27	0.0
psi_plus	7,27	0.0
psi_plus	8,27	0.0
psi_plus	9,27	0.0
psi_plus	10,27	0.0
psi_plus	11,27	0.0
psi_plus	12,27	0.0
psi_plus	13,27	0.0
psi_plus	14,27	0.0
psi_plus	15,27	0.0
psi_plus	16,27	0.0
psi_plus	17,27	0.0
psi_plus	18,27	0.0
psi_plus	19,27	0.0
psi_plus	20,27	0.0
psi_plus	1,28	0.0
psi_plus	2,28	0.0
psi_plus	3,28	0.0
psi_plus	4,28	0.0
psi_plus	5,28	0.0
psi_plus	6,28	0.0
psi_plus	7,28	0.0
psi_plus	8,28	0.0
psi_plus	9,28	0.0
psi_plus	10,28	0.0
psi_plus	11,28	0.0
psi_plus	12,28	0.0
psi_plus	13,28	0.0
psi_plus	14,28	0.0
psi_plus	15,28	0.0
psi_plus	16,28	0.0
psi_plus	17,28	0.0
psi_plus	18,28	0.0
psi_plus	19,28	0.0
psi_plus	20,28	0.0
psi_plus	1,29	0.0
psi_plus	2,29	0.0
psi_plus	3,29	0.0
psi_plus	4,29	0.0
psi_plus	5,29	0.0
psi_plus	6,29	0.0
psi_plus	7,29	0.0
psi_plus	8,29	0.0
psi_plus	9,29	0.0
psi_plus	10,29	0.0
psi_plus	11,29	0.0
psi_plus	12,29	0.0
psi_plus	13,29	0.0
psi_plus	14,29	0.0
psi_plus	15,29	0.0
psi_plus	16,29	0.0
psi_plus	17,29	0.0
psi_plus	18,29	0.0
psi_plus	19,29	0.0
psi_plus	20,29	0.0
psi_plus	1,30	0.0
psi_plus	2,30	0.0
psi_plus	3,30	0.0
psi_plus	4,30	0.0
psi_plus	5,30	0.0
psi_plus	6,30	0.0
psi_plus	7,30	0.0
psi_plus	8,30	0.0
psi_plus	9,30	0.0
psi_plus	10,30	0.0
psi_plus	11,30	0.0
psi_plus	12,30	0.0
psi_plus	13,30	0.0
psi_plus	14,30	0.0
psi_plus	15,30	0.0
psi_plus	16,30	0.0
psi_plus	17,30	0.0
psi_plus	18,30	0.0
psi_plus	19,30	0.0
psi_plus	20,30	0.0
psi_plus	1,31	1.0
psi_plus	2,31	1.0
psi_plus	3,31	1.0
psi_plus	4,31	1.0
psi_plus	5,31	1.0
psi_plus	6,31	1.0
psi_plus	7,31	1.0
psi_plus	8,31	1.0
psi_plus	9,31	1.0
psi_plus	10,31	1.0
psi_plus	11,31	1.0
psi_plus	12,31	1.0
psi_plus	13,31	1.0
psi_plus	14,31	1.0
psi_plus	15,31	1.0
psi_plus	16,31	1.0
psi_plus	17,31	1.0
psi_plus	18,31	1.0
psi_plus	19,31	1.0
psi_plus	20,31	1.0
psi_plus	1,32	1.0
psi_plus	2,32	1.0
psi_plus	3,32	1.0
psi_plus	4,32	1.0
psi_plus	5,32	1.0
psi_plus	6,32	1.0
psi_plus	7,32	1.0
psi_plus	8,32	1.0
psi_plus	9,32	1.0
psi_plus	10,32	1.0
psi_plus	11,32	1.0
psi_plus	12,32	1.0
psi_plus	13,32	1.0
psi_plus	14,32	1.0
psi_plus	15,32	1.0
psi_plus	16,32	1.0
psi_plus	17,32	1.0
psi_plus	18,32	1.0
psi_plus	19,32	1.0
psi_plus	20,32	1.0
psi_plus	1,33	1.0
psi_plus	2,33	1.0
psi_plus	3,33	1.0
psi_plus	4,33	1.0
psi_plus	5,33	1.0
psi_plus	6,33	1.0
psi_plus	7,33	1.0
psi_plus	8,33	1.0
psi_plus	9,33	1.0
psi_plus	10,33	1.0
psi_plus	11,33	1.0
psi_plus	12,33	1.0
psi_plus	13,33	1.0
psi_plus	14,33	1.0
psi_plus	15,33	1.0
psi_plus	16,33	1.0
psi_plus	17,33	1.0
psi_plus	18,33	1.0
psi_plus	19,33	1.0
psi_plus	20,33	1.0
psi_plus	1,34	1.0
psi_plus	2,34	1.0
psi_plus	3,34	1.0
psi_plus	4,34	1.0
psi_plus	5,34	1.0
psi_plus	6,34	1.0
psi_plus	7,34	1.0
psi_plus	8,34	1.0
psi_plus	9,34	1.0
psi_plus	10,34	1.0
psi_plus	11,34	1.0
psi_plus	12,34	1.0
psi_plus	13,34	1.0
psi_plus	14,34	1.0
psi_plus	15,34	1.0
psi_plus	16,34	1.0
psi_plus	17,34	1.0
psi_plus	18,34	1.0
psi_plus	19,34	1.0
psi_plus	20,34	1.0
psi_plus	1,35	1.0
psi_plus	2,35	1.0
psi_plus	3,35	1.0
psi_plus	4,35	1.0
psi_plus	5,35	1.0
psi_plus	6,35	1.0
psi_plus	7,35	1.0
psi_plus	8,35	1.0
psi_plus	9,35	1.0
psi_plus	10,35	1.0
psi_plus	11,35	1.0
psi_plus	12,35	1.0
psi_plus	13,35	1.0
psi_plus	14,35	1.0
psi_plus	15,35	1.0
psi_plus	16,35	1.0
psi_plus	17,35	1.0
psi_plus	18,35	1.0
psi_plus	19,35	1.0
psi_plus	20,35	1.0
psi_plus	1,36	1.0
psi_plus	2,36	1.0
psi_plus	3,36	1.0
psi_plus	4,36	1.0
psi_plus	5,36	1.0
psi_plus	6,36	1.0
psi_plus	7,36	1.0
psi_plus	8,36	1.0
psi_plus	9,36	1.0
psi_plus	10,36	1.0
psi_plus	11,36	1.0
psi_plus	12,36	1.0
psi_plus	13,36	1.0
psi_plus	14,36	1.0
psi_plus	15,36	1.0
psi_plus	16,36	1.0
psi_plus	17,36	1.0
psi_plus	18,36	1.0
psi_plus	19,36	1.0
psi_plus	20,36	1.0
psi_plus	1,37	1.0
psi_plus	2,37	1.0
psi_plus	3,37	1.0
psi_plus	4,37	1.0
psi_plus	5,37	1.0
psi_plus	6,37	1.0
psi_plus	7,37	1.0
psi_plus	8,37	1.0
psi_plus	9,37	1.0
psi_plus	10,37	1.0
psi_plus	11,37	1.0
psi_plus	12,37	1.0
psi_plus	13,37	1.0
psi_plus	14,37	1.0
psi_plus	15,37	1.0
psi_plus	16,37	1.0
psi_plus	17,37	1.0
psi_plus	18,37	1.0
psi_plus	19,37	1.0
psi_plus	20,37	1.0
psi_plus	1,38	1.0
psi_plus	2,38	1.0
psi_plus	3,38	1.0
psi_plus	4,38	1.0
psi_plus	5,38	1.0
psi_plus	6,38	1.0
psi_plus	7,38	1.0
psi_plus	8,38	1.0
psi_plus	9,38	1.0
psi_plus	10,38	1.0
psi_plus	11,38	1.0
psi_plus	12,38	1.0
psi_plus	13,38	1.0
psi_plus	14,38	1.0
psi_plus	15,38	1.0
psi_plus	16,38	1.0
psi_plus	17,38	1.0
psi_plus	18,38	1.0
psi_plus	19,38	1.0
psi_plus	20,38	1.0
psi_plus	1,39	1.0
psi_plus	2,39	1.0
psi_plus	3,39	1.0
psi_plus	4,39	1.0
psi_plus	5,39	1.0
psi_plus	6,39	1.0
psi_plus	7,39	1.0
psi_plus	8,39	1.0
psi_plus	9,39	1.0
psi_plus	10,39	1.0
psi_plus	11,39	1.0
psi_plus	12,39	1.0
psi_plus	13,39	1.0
psi_plus	14,39	1.0
psi_plus	15,39	1.0
psi_plus	16,39	1.0
psi_plus	17,39	1.0
psi_plus	18,39	1.0
psi_plus	19,39	1.0
psi_plus	20,39	1.0
psi_plus	1,40	1.0
psi_plus	2,40	1.0
psi_plus	3,40	1.0
psi_plus	4,40	1.0
psi_plus	5,40	1.0
psi_plus	6,40	1.0
psi_plus	7,40	1.0
psi_plus	8,40	1.0
psi_plus	9,40	1.0
psi_plus	10,40	1.0
psi_plus	11,40	1.0
psi_plus	12,40	1.0
psi_plus	13,40	1.0
psi_plus	14,40	1.0
psi_plus	15,40	1.0
psi_plus	16,40	1.0
psi_plus	17,40	1.0
psi_plus	18,40	1.0
psi_plus	19,40	1.0
psi_plus	20,40	1.0
psi_plus	1,41	1.0
psi_plus	2,41	1.0
psi_plus	3,41	1.0
psi_plus	4,41	1.0
psi_plus	5,41	1.0
psi_plus	6,41	1.0
psi_plus	7,41	1.0
psi_plus	8,41	1.0
psi_plus	9,41	1.0
psi_plus	10,41	1.0
psi_plus	11,41	1.0
psi_plus	12,41	1.0
psi_plus	13,41	1.0
psi_plus	14,41	1.0
psi_plus	15,41	1.0
psi_plus	16,41	1.0
psi_plus	17,41	1.0
psi_plus	18,41	1.0
psi_plus	19,41	1.0
psi_plus	20,41	1.0
psi_plus	1,42	1.0
psi_plus	2,42	1.0
psi_plus	3,42	1.0
psi_plus	4,42	1.0
psi_plus	5,42	1.0
psi_plus	6,42	1.0
psi_plus	7,42	1.0
psi_plus	8,42	1.0
psi_plus	9,42	1.0
psi_plus	10,42	1.0
psi_plus	11,42	1.0
psi_plus	12,42	1.0
psi_plus	13,42	1.0
psi_plus	14,42	1.0
psi_plus	15,42	1.0
psi_plus	16,42	1.0
psi_plus	17,42	1.0
psi_plus	18,42	1.0
psi_plus	19,42	1.0
psi_plus	20,42	1.0
psi_plus	1,43	1.0
psi_plus	2,43	1.0
psi_plus	3,43	1.0
psi_plus	4,43	1.0
psi_plus	5,43	1.0
psi_plus	6,43	1.0
psi_plus	7,43	1.0
psi_plus	8,43	1.0
psi_plus	9,43	1.0
psi_plus	10,43	1.0
psi_plus	11,43	1.0
psi_plus	12,43	1.0
psi_plus	13,43	1.0
psi_plus	14,43	1.0
psi_plus	15,43	1.0
psi_plus	16,43	1.0
psi_plus	17,43	1.0
psi_plus	18,43	1.0
psi_plus	19,43	1.0
psi_plus	20,43	1.0
psi_plus	1,44	1.0
psi_plus	2,44	1.0
psi_plus	3,44	1.0
psi_plus	4,44	1.0
psi_plus	5,44	1.0
psi_plus	6,44	1.0
psi_plus	7,44	1.0
psi_plus	8,44	1.0
psi_plus	9,44	1.0
psi_plus	10,44	1.0
psi_plus	11,44	1.0
psi_plus	12,44	1.0
psi_plus	13,44	1.0
psi_plus	14,44	1.0
psi_plus	15,44	1.0
psi_plus	16,44	1.0
psi_plus	17,44	1.0
psi_plus	18,44	1.0
psi_plus	19,44	1.0
psi_plus	20,44	1.0
psi_plus	1,45	0.0
psi_plus	2,45	0.0
psi_plus	3,45	0.0
psi_plus	4,45	0.0
psi_plus	5,45	0.0
psi_plus	6,45	0.0
psi_plus	7,45	0.0
psi_plus	8,45	0.0
psi_plus	9,45	0.0
psi_plus	10,45	0.0
psi_plus	11,45	0.0
psi_plus	12,45	0.0
psi_plus	13,45	0.0
psi_plus	14,45	0.0
psi_plus	15,45	0.0
psi_plus	16,45	0.0
psi_plus	17,45	0.0
psi_plus	18,45	0.0
psi_plus	19,45	0.0
psi_plus	20,45	0.0
psi_plus	1,46	0.0
psi_plus	2,46	0.0
psi_plus	3,46	0.0
psi_plus	4,46	0.0
psi_plus	5,46	0.0
psi_plus	6,46	0.0
psi_plus	7,46	0.0
psi_plus	8,46	0.0
psi_plus	9,46	0.0
psi_plus	10,46	0.0
psi_plus	11,46	0.0
psi_plus	12,46	0.0
psi_plus	13,46	0.0
psi_plus	14,46	0.0
psi_plus	15,46	0.0
psi_plus	16,46	0.0
psi_plus	17,46	0.0
psi_plus	18,46	0.0
psi_plus	19,46	0.0
psi_plus	20,46	0.0
psi_plus	1,47	0.0
psi_plus	2,47	0.0
psi_plus	3,47	0.0
psi_plus	4,47	0.0
psi_plus	5,47	0.0
psi_plus	6,47	0.0
psi_plus	7,47	0.0
psi_plus	8,47	0.0
psi_plus	9,47	0.0
psi_plus	10,47	0.0
psi_plus	11,47	0.0
psi_plus	12,47	0.0
psi_plus	13,47	0.0
psi_plus	14,47	0.0
psi_plus	15,47	0.0
psi_plus	16,47	0.0
psi_plus	17,47	0.0
psi_plus	18,47	0.0
psi_plus	19,47	0.0
psi_plus	20,47	0.0
psi_plus	1,48	0.0
psi_plus	2,48	0.0
psi_plus	3,48	0.0
psi_plus	4,48	0.0
psi_plus	5,48	0.0
psi_plus	6,48	0.0
psi_plus	7,48	0.0
psi_plus	8,48	0.0
psi_plus	9,48	0.0
psi_plus	10,48	0.0
psi_plus	11,48	0.0
psi_plus	12,48	0.0
psi_plus	13,48	0.0
psi_plus	14,48	0.0
psi_plus	15,48	0.0
psi_plus	16,48	0.0
psi_plus	17,48	0.0
psi_plus	18,48	0.0
psi_plus	19,48	0.0
psi_plus	20,48	0.0
psi_plus	1,49	0.0
psi_plus	2,49	0.0
psi_plus	3,49	0.0
psi_plus	4,49	0.0
psi_plus	5,49	0.0
psi_plus	6,49	0.0
psi_plus	7,49	0.0
psi_plus	8,49	0.0
psi_plus	9,49	0.0
psi_plus	10,49	0.0
psi_plus	11,49	0.0
psi_plus	12,49	0.0
psi_plus	13,49	0.0
psi_plus	14,49	0.0
psi_plus	15,49	0.0
psi_plus	16,49	0.0
psi_plus	17,49	0.0
psi_plus	18,49	0.0
psi_plus	19,49	0.0
psi_plus	20,49	0.0
psi_plus	1,50	0.0
psi_plus	2,50	0.0
psi_plus	3,50	0.0
psi_plus	4,50	0.0
psi_plus	5,50	0.0
psi_plus	6,50	0.0
psi_plus	7,50	0.0
psi_plus	8,50	0.0
psi_plus	9,50	0.0
psi_plus	10,50	0.0
psi_plus	11,50	0.0
psi_plus	12,50	0.0
psi_plus	13,50	0.0
psi_plus	14,50	0.0
psi_plus	15,50	0.0
psi_plus	16,50	0.0
psi_plus	17,50	0.0
psi_plus	18,50	0.0
psi_plus	19,50	0.0
psi_plus	20,50	0.0
psi_plus	1,51	0.0
psi_plus	2,51	0.0
psi_plus	3,51	0.0
psi_plus	4,51	0.0
psi_plus	5,51	0.0
psi_plus	6,51	0.0
psi_plus	7,51	0.0
psi_plus	8,51	0.0
psi_plus	9,51	0.0
psi_plus	10,51	0.0
psi_plus	11,51	0.0
psi_plus	12,51	0.0
psi_plus	13,51	0.0
psi_plus	14,51	0.0
psi_plus	15,51	0.0
psi_plus	16,51	0.0
psi_plus	17,51	0.0
psi_plus	18,51	0.0
psi_plus	19,51	0.0
psi_plus	20,51	0.0
psi_plus	1,52	0.0
psi_plus	2,52	0.0
psi_plus	3,52	0.0
psi_plus	4,52	0.0
psi_plus	5,52	0.0
psi_plus	6,52	0.0
psi_plus	7,52	0.0
psi_plus	8,52	0.0
psi_plus	9,52	0.0
psi_plus	10,52	0.0
psi_plus	11,52	0.0
psi_plus	12,52	0.0
psi_plus	13,52	0.0
psi_plus	14,52	0.0
psi_plus	15,52	0.0
psi_plus	16,52	0.0
psi_plus	17,52	0.0
psi_plus	18,52	0.0
psi_plus	19,52	0.0
psi_plus	20,52	0.0
psi_plus	1,53	0.0
psi_plus	2,53	0.0
psi_plus	3,53	0.0
psi_plus	4,53	0.0
psi_plus	5,53	0.0
psi_plus	6,53	0.0
psi_plus	7,53	0.0
psi_plus	8,53	0.0
psi_plus	9,53	0.0
psi_plus	10,53	0.0
psi_plus	11,53	0.0
psi_plus	12,53	0.0
psi_plus	13,53	0.0
psi_plus	14,53	0.0
psi_plus	15,53	0.0
psi_plus	16,53	0.0
psi_plus	17,53	0.0
psi_plus	18,53	0.0
psi_plus	19,53	0.0
psi_plus	20,53	0.0
psi_plus	1,54	0.0
psi_plus	2,54	0.0
psi_plus	3,54	0.0
psi_plus	4,54	0.0
psi_plus	5,54	0.0
psi_plus	6,54	0.0
psi_plus	7,54	0.0
psi_plus	8,54	0.0
psi_plus	9,54	0.0
psi_plus	10,54	0.0
psi_plus	11,54	0.0
psi_plus	12,54	0.0
psi_plus	13,54	0.0
psi_plus	14,54	0.0
psi_plus	15,54	0.0
psi_plus	16,54	0.0
psi_plus	17,54	0.0
psi_plus	18,54	0.0
psi_plus	19,54	0.0
psi_plus	20,54	0.0
psi_plus	1,55	1.0
psi_plus	2,55	1.0
psi_plus	3,55	1.0
psi_plus	4,55	1.0
psi_plus	5,55	1.0
psi_plus	6,55	1.0
psi_plus	7,55	1.0
psi_plus	8,55	1.0
psi_plus	9,55	1.0
psi_plus	10,55	1.0
psi_plus	11,55	1.0
psi_plus	12,55	1.0
psi_plus	13,55	1.0
psi_plus	14,55	1.0
psi_plus	15,55	1.0
psi_plus	16,55	1.0
psi_plus	17,55	1.0
psi_plus	18,55	1.0
psi_plus	19,55	1.0
psi_plus	20,55	1.0
psi_plus	1,56	1.0
psi_plus	2,56	1.0
psi_plus	3,56	1.0
psi_plus	4,56	1.0
psi_plus	5,56	1.0
psi_plus	6,56	1.0
psi_plus	7,56	1.0
psi_plus	8,56	1.0
psi_plus	9,56	1.0
psi_plus	10,56	1.0
psi_plus	11,56	1.0
psi_plus	12,56	1.0
psi_plus	13,56	1.0
psi_plus	14,56	1.0
psi_plus	15,56	1.0
psi_plus	16,56	1.0
psi_plus	17,56	1.0
psi_plus	18,56	1.0
psi_plus	19,56	1.0
psi_plus	20,56	1.0
psi_plus	1,57	1.0
psi_plus	2,57	1.0
psi_plus	3,57	1.0
psi_plus	4,57	1.0
psi_plus	5,57	1.0
psi_plus	6,57	1.0
psi_plus	7,57	1.0
psi_plus	8,57	1.0
psi_plus	9,57	1.0
psi_plus	10,57	1.0
psi_plus	11,57	1.0
psi_plus	12,57	1.0
psi_plus	13,57	1.0
psi_plus	14,57	1.0
psi_plus	15,57	1.0
psi_plus	16,57	1.0
psi_plus	17,57	1.0
psi_plus	18,57	1.0
psi_plus	19,57	1.0
psi_plus	20,57	1.0
psi_plus	1,58	1.0
psi_plus	2,58	1.0
psi_plus	3,58	1.0
psi_plus	4,58	1.0
psi_plus	5,58	1.0
psi_plus	6,58	1.0
psi_plus	7,58	1.0
psi_plus	8,58	1.0
psi_plus	9,58	1.0
psi_plus	10,58	1.0
psi_plus	11,58	1.0
psi_plus	12,58	1.0
psi_plus	13,58	1.0
psi_plus	14,58	1.0
psi_plus	15,58	1.0
psi_plus	16,58	1.0
psi_plus	17,58	1.0
psi_plus	18,58	1.0
psi_plus	19,58	1.0
psi_plus	20,58	1.0
psi_plus	1,59	1.0
psi_plus	2,59	1.0
psi_plus	3,59	1.0
psi_plus	4,59	1.0
psi_plus	5,59	1.0
psi_plus	6,59	1.0
psi_plus	7,59	1.0
psi_plus	8,59	1.0
psi_plus	9,59	1.0
psi_plus	10,59	1.0
psi_plus	11,59	1.0
psi_plus	12,59	1.0
psi_plus	13,59	1.0
psi_plus	14,59	1.0
psi_plus	15,59	1.0
psi_plus	16,59	1.0
psi_plus	17,59	1.0
psi_plus	18,59	1.0
psi_plus	19,59	1.0
psi_plus	20,59	1.0
psi_plus	1,60	1.0
psi_plus	2,60	1.0
psi_plus	3,60	1.0
psi_plus	4,60	1.0
psi_plus	5,60	1.0
psi_plus	6,60	1.0
psi_plus	7,60	1.0
psi_plus	8,60	1.0
psi_plus	9,60	1.0
psi_plus	10,60	1.0
psi_plus	11,60	1.0
psi_plus	12,60	1.0
psi_plus	13,60	1.0
psi_plus	14,60	1.0
psi_plus	15,60	1.0
psi_plus	16,60	1.0
psi_plus	17,60	1.0
psi_plus	18,60	1.0
psi_plus	19,60	1.0
psi_plus	20,60	1.0
psi_plus	1,61	1.0
psi_plus	2,61	1.0
psi_plus	3,61	1.0
psi_plus	4,61	1.0
psi_plus	5,61	1.0
psi_plus	6,61	1.0
psi_plus	7,61	1.0
psi_plus	8,61	1.0
psi_plus	9,61	1.0
psi_plus	10,61	1.0
psi_plus	11,61	1.0
psi_plus	12,61	1.0
psi_plus	13,61	1.0
psi_plus	14,61	1.0
psi_plus	15,61	1.0
psi_plus	16,61	1.0
psi_plus	17,61	1.0
psi_plus	18,61	1.0
psi_plus	19,61	1.0
psi_plus	20,61	1.0
psi_plus	1,62	1.0
psi_plus	2,62	1.0
psi_plus	3,62	1.0
psi_plus	4,62	1.0
psi_plus	5,62	1.0
psi_plus	6,62	1.0
psi_plus	7,62	1.0
psi_plus	8,62	1.0
psi_plus	9,62	1.0
psi_plus	10,62	1.0
psi_plus	11,62	1.0
psi_plus	12,62	1.0
psi_plus	13,62	1.0
psi_plus	14,62	1.0
psi_plus	15,62	1.0
psi_plus	16,62	1.0
psi_plus	17,62	1.0
psi_plus	18,62	1.0
psi_plus	19,62	1.0
psi_plus	20,62	1.0
psi_plus	1,63	1.0
psi_plus	2,63	1.0
psi_plus	3,63	1.0
psi_plus	4,63	1.0
psi_plus	5,63	1.0
psi_plus	6,63	1.0
psi_plus	7,63	1.0
psi_plus	8,63	1.0
psi_plus	9,63	1.0
psi_plus	10,63	1.0
psi_plus	11,63	1.0
psi_plus	12,63	1.0
psi_plus	13,63	1.0
psi_plus	14,63	1.0
psi_plus	15,63	1.0
psi_plus	16,63	1.0
psi_plus	17,63	1.0
psi_plus	18,63	1.0
psi_plus	19,63	1.0
psi_plus	20,63	1.0
psi_plus	1,64	1.0
psi_plus	2,64	1.0
psi_plus	3,64	1.0
psi_plus	4,64	1.0
psi_plus	5,64	1.0
psi_plus	6,64	1.0
psi_plus	7,64	1.0
psi_plus	8,64	1.0
psi_plus	9,64	1.0
psi_plus	10,64	1.0
psi_plus	11,64	1.0
psi_plus	12,64	1.0
psi_plus	13,64	1.0
psi_plus	14,64	1.0
psi_plus	15,64	1.0
psi_plus	16,64	1.0
psi_plus	17,64	1.0
psi_plus	18,64	1.0
psi_plus	19,64	1.0
psi_plus	20,64	1.0
psi_plus	1,65	1.0
psi_plus	2,65	1.0
psi_plus	3,65	1.0
psi_plus	4,65	1.0
psi_plus	5,65	1.0
psi_plus	6,65	1.0
psi_plus	7,65	1.0
psi_plus	8,65	1.0
psi_plus	9,65	1.0
psi_plus	10,65	1.0
psi_plus	11,65	1.0
psi_plus	12,65	1.0
psi_plus	13,65	1.0
psi_plus	14,65	1.0
psi_plus	15,65	1.0
psi_plus	16,65	1.0
psi_plus	17,65	1.0
psi_plus	18,65	1.0
psi_plus	19,65	1.0
psi_plus	20,65	1.0
psi_plus	1,66	1.0
psi_plus	2,66	1.0
psi_plus	3,66	1.0
psi_plus	4,66	1.0
psi_plus	5,66	1.0
psi_plus	6,66	1.0
psi_plus	7,66	1.0
psi_plus	8,66	1.0
psi_plus	9,66	1.0
psi_plus	10,66	1.0
psi_plus	11,66	1.0
psi_plus	12,66	1.0
psi_plus	13,66	1.0
psi_plus	14,66	1.0
psi_plus	15,66	1.0
psi_plus	16,66	1.0
psi_plus	17,66	1.0
psi_plus	18,66	1.0
psi_plus	19,66	1.0
psi_plus	20,66	1.0
psi_plus	1,67	1.0
psi_plus	2,67	1.0
psi_plus	3,67	1.0
psi_plus	4,67	1.0
psi_plus	5,67	1.0
psi_plus	6,67	1.0
psi_plus	7,67	1.0
psi_plus	8,67	1.0
psi_plus	9,67	1.0
psi_plus	10,67	1.0
psi_plus	11,67	1.0
psi_plus	12,67	1.0
psi_plus	13,67	1.0
psi_plus	14,67	1.0
psi_plus	15,67	1.0
psi_plus	16,67	1.0
psi_plus	17,67	1.0
psi_plus	18,67	1.0
psi_plus	19,67	1.0
psi_plus	20,67	1.0
psi_plus	1,68	1.0
psi_plus	2,68	1.0
psi_plus	3,68	1.0
psi_plus	4,68	1.0
psi_plus	5,68	1.0
psi_plus	6,68	1.0
psi_plus	7,68	1.0
psi_plus	8,68	1.0
psi_plus	9,68	1.0
psi_plus	10,68	1.0
psi_plus	11,68	1.0
psi_plus	12,68	1.0
psi_plus	13,68	1.0
psi_plus	14,68	1.0
psi_plus	15,68	1.0
psi_plus	16,68	1.0
psi_plus	17,68	1.0
psi_plus	18,68	1.0
psi_plus	19,68	1.0
psi_plus	20,68	1.0
psi_plus	1,69	0.0
psi_plus	2,69	0.0
psi_plus	3,69	0.0
psi_plus	4,69	0.0
psi_plus	5,69	0.0
psi_plus	6,69	0.0
psi_plus	7,69	0.0
psi_plus	8,69	0.0
psi_plus	9,69	0.0
psi_plus	10,69	0.0
psi_plus	11,69	0.0
psi_plus	12,69	0.0
psi_plus	13,69	0.0
psi_plus	14,69	0.0
psi_plus	15,69	0.0
psi_plus	16,69	0.0
psi_plus	17,69	0.0
psi_plus	18,69	0.0
psi_plus	19,69	0.0
psi_plus	20,69	0.0
psi_plus	1,70	0.0
psi_plus	2,70	0.0
psi_plus	3,70	0.0
psi_plus	4,70	0.0
psi_plus	5,70	0.0
psi_plus	6,70	0.0
psi_plus	7,70	0.0
psi_plus	8,70	0.0
psi_plus	9,70	0.0
psi_plus	10,70	0.0
psi_plus	11,70	0.0
psi_plus	12,70	0.0
psi_plus	13,70	0.0
psi_plus	14,70	0.0
psi_plus	15,70	0.0
psi_plus	16,70	0.0
psi_plus	17,70	0.0
psi_plus	18,70	0.0
psi_plus	19,70	0.0
psi_plus	20,70	0.0
psi_plus	1,71	0.0
psi_plus	2,71	0.0
psi_plus	3,71	0.0
psi_plus	4,71	0.0
psi_plus	5,71	0.0
psi_plus	6,71	0.0
psi_plus	7,71	0.0
psi_plus	8,71	0.0
psi_plus	9,71	0.0
psi_plus	10,71	0.0
psi_plus	11,71	0.0
psi_plus	12,71	0.0
psi_plus	13,71	0.0
psi_plus	14,71	0.0
psi_plus	15,71	0.0
psi_plus	16,71	0.0
psi_plus	17,71	0.0
psi_plus	18,71	0.0
psi_plus	19,71	0.0
psi_plus	20,71	0.0
psi_plus	1,72	0.0
psi_plus	2,72	0.0
psi_plus	3,72	0.0
psi_plus	4,72	0.0
psi_plus	5,72	0.0
psi_plus	6,72	0.0
psi_plus	7,72	0.0
psi_plus	8,72	0.0
psi_plus	9,72	0.0
psi_plus	10,72	0.0
psi_plus	11,72	0.0
psi_plus	12,72	0.0
psi_plus	13,72	0.0
psi_plus	14,72	0.0
psi_plus	15,72	0.0
psi_plus	16,72	0.0
psi_plus	17,72	0.0
psi_plus	18,72	0.0
psi_plus	19,72	0.0
psi_plus	20,72	0.0
psi_plus	1,73	0.0
psi_plus	2,73	0.0
psi_plus	3,73	0.0
psi_plus	4,73	0.0
psi_plus	5,73	0.0
psi_plus	6,73	0.0
psi_plus	7,73	0.0
psi_plus	8,73	0.0
psi_plus	9,73	0.0
psi_plus	10,73	0.0
psi_plus	11,73	0.0
psi_plus	12,73	0.0
psi_plus	13,73	0.0
psi_plus	14,73	0.0
psi_plus	15,73	0.0
psi_plus	16,73	0.0
psi_plus	17,73	0.0
psi_plus	18,73	0.0
psi_plus	19,73	0.0
psi_plus	20,73	0.0
psi_plus	1,74	0.0
psi_plus	2,74	0.0
psi_plus	3,74	0.0
psi_plus	4,74	0.0
psi_plus	5,74	0.0
psi_plus	6,74	0.0
psi_plus	7,74	0.0
psi_plus	8,74	0.0
psi_plus	9,74	0.0
psi_plus	10,74	0.0
psi_plus	11,74	0.0
psi_plus	12,74	0.0
psi_plus	13,74	0.0
psi_plus	14,74	0.0
psi_plus	15,74	0.0
psi_plus	16,74	0.0
psi_plus	17,74	0.0
psi_plus	18,74	0.0
psi_plus	19,74	0.0
psi_plus	20,74	0.0
psi_plus	1,75	0.0
psi_plus	2,75	0.0
psi_plus	3,75	0.0
psi_plus	4,75	0.0
psi_plus	5,75	0.0
psi_plus	6,75	0.0
psi_plus	7,75	0.0
psi_plus	8,75	0.0
psi_plus	9,75	0.0
psi_plus	10,75	0.0
psi_plus	11,75	0.0
psi_plus	12,75	0.0
psi_plus	13,75	0.0
psi_plus	14,75	0.0
psi_plus	15,75	0.0
psi_plus	16,75	0.0
psi_plus	17,75	0.0
psi_plus	18,75	0.0
psi_plus	19,75	0.0
psi_plus	20,75	0.0
psi_plus	1,76	0.0
psi_plus	2,76	0.0
psi_plus	3,76	0.0
psi_plus	4,76	0.0
psi_plus	5,76	0.0
psi_plus	6,76	0.0
psi_plus	7,76	0.0
psi_plus	8,76	0.0
psi_plus	9,76	0.0
psi_plus	10,76	0.0
psi_plus	11,76	0.0
psi_plus	12,76	0.0
psi_plus	13,76	0.0
psi_plus	14,76	0.0
psi_plus	15,76	0.0
psi_plus	16,76	0.0
psi_plus	17,76	0.0
psi_plus	18,76	0.0
psi_plus	19,76	0.0
psi_plus	20,76	0.0
psi_plus	1,77	0.0
psi_plus	2,77	0.0
psi_plus	3,77	0.0
psi_plus	4,77	0.0
psi_plus	5,77	0.0
psi_plus	6,77	0.0
psi_plus	7,77	0.0
psi_plus	8,77	0.0
psi_plus	9,77	0.0
psi_plus	10,77	0.0
psi_plus	11,77	0.0
psi_plus	12,77	0.0
psi_plus	13,77	0.0
psi_plus	14,77	0.0
psi_plus	15,77	0.0
psi_plus	16,77	0.0
psi_plus	17,77	0.0
psi_plus	18,77	0.0
psi_plus	19,77	0.0
psi_plus	20,77	0.0
psi_plus	1,78	0.0
psi_plus	2,78	0.0
psi_plus	3,78	0.0
psi_plus	4,78	0.0
psi_plus	5,78	0.0
psi_plus	6,78	0.0
psi_plus	7,78	0.0
psi_plus	8,78	0.0
psi_plus	9,78	0.0
psi_plus	10,78	0.0
psi_plus	11,78	0.0
psi_plus	12,78	0.0
psi_plus	13,78	0.0
psi_plus	14,78	0.0
psi_plus	15,78	0.0
psi_plus	16,78	0.0
psi_plus	17,78	0.0
psi_plus	18,78	0.0
psi_plus	19,78	0.0
psi_plus	20,78	0.0
psi_plus	1,79	1.0
psi_plus	2,79	1.0
psi_plus	3,79	1.0
psi_plus	4,79	1.0
psi_plus	5,79	1.0
psi_plus	6,79	1.0
psi_plus	7,79	1.0
psi_plus	8,79	1.0
psi_plus	9,79	1.0
psi_plus	10,79	1.0
psi_plus	11,79	1.0
psi_plus	12,79	1.0
psi_plus	13,79	1.0
psi_plus	14,79	1.0
psi_plus	15,79	1.0
psi_plus	16,79	1.0
psi_plus	17,79	1.0
psi_plus	18,79	1.0
psi_plus	19,79	1.0
psi_plus	20,79	1.0
psi_plus	1,80	1.0
psi_plus	2,80	1.0
psi_plus	3,80	1.0
psi_plus	4,80	1.0
psi_plus	5,80	1.0
psi_plus	6,80	1.0
psi_plus	7,80	1.0
psi_plus	8,80	1.0
psi_plus	9,80	1.0
psi_plus	10,80	1.0
psi_plus	11,80	1.0
psi_plus	12,80	1.0
psi_plus	13,80	1.0
psi_plus	14,80	1.0
psi_plus	15,80	1.0
psi_plus	16,80	1.0
psi_plus	17,80	1.0
psi_plus	18,80	1.0
psi_plus	19,80	1.0
psi_plus	20,80	1.0
psi_plus	1,81	1.0
psi_plus	2,81	1.0
psi_plus	3,81	1.0
psi_plus	4,81	1.0
psi_plus	5,81	1.0
psi_plus	6,81	1.0
psi_plus	7,81	1.0
psi_plus	8,81	1.0
psi_plus	9,81	1.0
psi_plus	10,81	1.0
psi_plus	11,81	1.0
psi_plus	12,81	1.0
psi_plus	13,81	1.0
psi_plus	14,81	1.0
psi_plus	15,81	1.0
psi_plus	16,81	1.0
psi_plus	17,81	1.0
psi_plus	18,81	1.0
psi_plus	19,81	1.0
psi_plus	20,81	1.0
psi_plus	1,82	1.0
psi_plus	2,82	1.0
psi_plus	3,82	1.0
psi_plus	4,82	1.0
psi_plus	5,82	1.0
psi_plus	6,82	1.0
psi_plus	7,82	1.0
psi_plus	8,82	1.0
psi_plus	9,82	1.0
psi_plus	10,82	1.0
psi_plus	11,82	1.0
psi_plus	12,82	1.0
psi_plus	13,82	1.0
psi_plus	14,82	1.0
psi_plus	15,82	1.0
psi_plus	16,82	1.0
psi_plus	17,82	1.0
psi_plus	18,82	1.0
psi_plus	19,82	1.0
psi_plus	20,82	1.0
psi_plus	1,83	1.0
psi_plus	2,83	1.0
psi_plus	3,83	1.0
psi_plus	4,83	1.0
psi_plus	5,83	1.0
psi_plus	6,83	1.0
psi_plus	7,83	1.0
psi_plus	8,83	1.0
psi_plus	9,83	1.0
psi_plus	10,83	1.0
psi_plus	11,83	1.0
psi_plus	12,83	1.0
psi_plus	13,83	1.0
psi_plus	14,83	1.0
psi_plus	15,83	1.0
psi_plus	16,83	1.0
psi_plus	17,83	1.0
psi_plus	18,83	1.0
psi_plus	19,83	1.0
psi_plus	20,83	1.0
psi_plus	1,84	1.0
psi_plus	2,84	1.0
psi_plus	3,84	1.0
psi_plus	4,84	1.0
psi_plus	5,84	1.0
psi_plus	6,84	1.0
psi_plus	7,84	1.0
psi_plus	8,84	1.0
psi_plus	9,84	1.0
psi_plus	10,84	1.0
psi_plus	11,84	1.0
psi_plus	12,84	1.0
psi_plus	13,84	1.0
psi_plus	14,84	1.0
psi_plus	15,84	1.0
psi_plus	16,84	1.0
psi_plus	17,84	1.0
psi_plus	18,84	1.0
psi_plus	19,84	1.0
psi_plus	20,84	1.0
psi_plus	1,85	1.0
psi_plus	2,85	1.0
psi_plus	3,85	1.0
psi_plus	4,85	1.0
psi_plus	5,85	1.0
psi_plus	6,85	1.0
psi_plus	7,85	1.0
psi_plus	8,85	1.0
psi_plus	9,85	1.0
psi_plus	10,85	1.0
psi_plus	11,85	1.0
psi_plus	12,85	1.0
psi_plus	13,85	1.0
psi_plus	14,85	1.0
psi_plus	15,85	1.0
psi_plus	16,85	1.0
psi_plus	17,85	1.0
psi_plus	18,85	1.0
psi_plus	19,85	1.0
psi_plus	20,85	1.0
psi_plus	1,86	1.0
psi_plus	2,86	1.0
psi_plus	3,86	1.0
psi_plus	4,86	1.0
psi_plus	5,86	1.0
psi_plus	6,86	1.0
psi_plus	7,86	1.0
psi_plus	8,86	1.0
psi_plus	9,86	1.0
psi_plus	10,86	1.0
psi_plus	11,86	1.0
psi_plus	12,86	1.0
psi_plus	13,86	1.0
psi_plus	14,86	1.0
psi_plus	15,86	1.0
psi_plus	16,86	1.0
psi_plus	17,86	1.0
psi_plus	18,86	1.0
psi_plus	19,86	1.0
psi_plus	20,86	1.0
psi_plus	1,87	1.0
psi_plus	2,87	1.0
psi_plus	3,87	1.0
psi_plus	4,87	1.0
psi_plus	5,87	1.0
psi_plus	6,87	1.0
psi_plus	7,87	1.0
psi_plus	8,87	1.0
psi_plus	9,87	1.0
psi_plus	10,87	1.0
psi_plus	11,87	1.0
psi_plus	12,87	1.0
psi_plus	13,87	1.0
psi_plus	14,87	1.0
psi_plus	15,87	1.0
psi_plus	16,87	1.0
psi_plus	17,87	1.0
psi_plus	18,87	1.0
psi_plus	19,87	1.0
psi_plus	20,87	1.0
psi_plus	1,88	1.0
psi_plus	2,88	1.0
psi_plus	3,88	1.0
psi_plus	4,88	1.0
psi_plus	5,88	1.0
psi_plus	6,88	1.0
psi_plus	7,88	1.0
psi_plus	8,88	1.0
psi_plus	9,88	1.0
psi_plus	10,88	1.0
psi_plus	11,88	1.0
psi_plus	12,88	1.0
psi_plus	13,88	1.0
psi_plus	14,88	1.0
psi_plus	15,88	1.0
psi_plus	16,88	1.0
psi_plus	17,88	1.0
psi_plus	18,88	1.0
psi_plus	19,88	1.0
psi_plus	20,88	1.0
psi_plus	1,89	1.0
psi_plus	2,89	1.0
psi_plus	3,89	1.0
psi_plus	4,89	1.0
psi_plus	5,89	1.0
psi_plus	6,89	1.0
psi_plus	7,89	1.0
psi_plus	8,89	1.0
psi_plus	9,89	1.0
psi_plus	10,89	1.0
psi_plus	11,89	1.0
psi_plus	12,89	1.0
psi_plus	13,89	1.0
psi_plus	14,89	1.0
psi_plus	15,89	1.0
psi_plus	16,89	1.0
psi_plus	17,89	1.0
psi_plus	18,89	1.0
psi_plus	19,89	1.0
psi_plus	20,89	1.0
psi_plus	1,90	1.0
psi_plus	2,90	1.0
psi_plus	3,90	1.0
psi_plus	4,90	1.0
psi_plus	5,90	1.0
psi_plus	6,90	1.0
psi_plus	7,90	1.0
psi_plus	8,90	1.0
psi_plus	9,90	1.0
psi_plus	10,90	1.0
psi_plus	11,90	1.0
psi_plus	12,90	1.0
psi_plus	13,90	1.0
psi_plus	14,90	1.0
psi_plus	15,90	1.0
psi_plus	16,90	1.0
psi_plus	17,90	1.0
psi_plus	18,90	1.0
psi_plus	19,90	1.0
psi_plus	20,90	1.0
psi_plus	1,91	1.0
psi_plus	2,91	1.0
psi_plus	3,91	1.0
psi_plus	4,91	1.0
psi_plus	5,91	1.0
psi_plus	6,91	1.0
psi_plus	7,91	1.0
psi_plus	8,91	1.0
psi_plus	9,91	1.0
psi_plus	10,91	1.0
psi_plus	11,91	1.0
psi_plus	12,91	1.0
psi_plus	13,91	1.0
psi_plus	14,91	1.0
psi_plus	15,91	1.0
psi_plus	16,91	1.0
psi_plus	17,91	1.0
psi_plus	18,91	1.0
psi_plus	19,91	1.0
psi_plus	20,91	1.0
psi_plus	1,92	1.0
psi_plus	2,92	1.0
psi_plus	3,92	1.0
psi_plus	4,92	1.0
psi_plus	5,92	1.0
psi_plus	6,92	1.0
psi_plus	7,92	1.0
psi_plus	8,92	1.0
psi_plus	9,92	1.0
psi_plus	10,92	1.0
psi_plus	11,92	1.0
psi_plus	12,92	1.0
psi_plus	13,92	1.0
psi_plus	14,92	1.0
psi_plus	15,92	1.0
psi_plus	16,92	1.0
psi_plus	17,92	1.0
psi_plus	18,92	1.0
psi_plus	19,92	1.0
psi_plus	20,92	1.0
psi_plus	1,93	0.0
psi_plus	2,93	0.0
psi_plus	3,93	0.0
psi_plus	4,93	0.0
psi_plus	5,93	0.0
psi_plus	6,93	0.0
psi_plus	7,93	0.0
psi_plus	8,93	0.0
psi_plus	9,93	0.0
psi_plus	10,93	0.0
psi_plus	11,93	0.0
psi_plus	12,93	0.0
psi_plus	13,93	0.0
psi_plus	14,93	0.0
psi_plus	15,93	0.0
psi_plus	16,93	0.0
psi_plus	17,93	0.0
psi_plus	18,93	0.0
psi_plus	19,93	0.0
psi_plus	20,93	0.0
psi_plus	1,94	0.0
psi_plus	2,94	0.0
psi_plus	3,94	0.0
psi_plus	4,94	0.0
psi_plus	5,94	0.0
psi_plus	6,94	0.0
psi_plus	7,94	0.0
psi_plus	8,94	0.0
psi_plus	9,94	0.0
psi_plus	10,94	0.0
psi_plus	11,94	0.0
psi_plus	12,94	0.0
psi_plus	13,94	0.0
psi_plus	14,94	0.0
psi_plus	15,94	0.0
psi_plus	16,94	0.0
psi_plus	17,94	0.0
psi_plus	18,94	0.0
psi_plus	19,94	0.0
psi_plus	20,94	0.0
psi_plus	1,95	0.0
psi_plus	2,95	0.0
psi_plus	3,95	0.0
psi_plus	4,95	0.0
psi_plus	5,95	0.0
psi_plus	6,95	0.0
psi_plus	7,95	0.0
psi_plus	8,95	0.0
psi_plus	9,95	0.0
psi_plus	10,95	0.0
psi_plus	11,95	0.0
psi_plus	12,95	0.0
psi_plus	13,95	0.0
psi_plus	14,95	0.0
psi_plus	15,95	0.0
psi_plus	16,95	0.0
psi_plus	17,95	0.0
psi_plus	18,95	0.0
psi_plus	19,95	0.0
psi_plus	20,95	0.0
psi_plus	1,96	0.0
psi_plus	2,96	0.0
psi_plus	3,96	0.0
psi_plus	4,96	0.0
psi_plus	5,96	0.0
psi_plus	6,96	0.0
psi_plus	7,96	0.0
psi_plus	8,96	0.0
psi_plus	9,96	0.0
psi_plus	10,96	0.0
psi_plus	11,96	0.0
psi_plus	12,96	0.0
psi_plus	13,96	0.0
psi_plus	14,96	0.0
psi_plus	15,96	0.0
psi_plus	16,96	0.0
psi_plus	17,96	0.0
psi_plus	18,96	0.0
psi_plus	19,96	0.0
psi_plus	20,96	0.0
theta_t	scalar	1.0
varpi_wt_plus	1,1	1.0
varpi_wt_plus	2,1	1.0
varpi_wt_plus	3,1	1.0
varpi_wt_plus	4,1	1.0
varpi_wt_plus	5,1	1.0
varpi_wt_plus	1,2	1.0
varpi_wt_plus	2,2	1.0
varpi_wt_plus	3,2	1.0
varpi_wt_plus	4,2	1.0
varpi_wt_plus	5,2	1.0
varpi_wt_plus	1,3	1.0
varpi_wt_plus	2,3	1.0
varpi_wt_plus	3,3	1.0
varpi_wt_plus	4,3	1.0
varpi_wt_plus	5,3	1.0
varpi_wt_plus	1,4	1.0
varpi_wt_plus	2,4	1.0
varpi_wt_plus	3,4	1.0
varpi_wt_plus	4,4	1.0
varpi_wt_plus	5,4	1.0
varpi_wt_plus	1,5	1.0
varpi_wt_plus	2,5	1.0
varpi_wt_plus	3,5	1.0
varpi_wt_plus	4,5	1.0
varpi_wt_plus	5,5	1.0
varpi_wt_plus	1,6	1.0
varpi_wt_plus	2,6	1.0
varpi_wt_plus	3,6	1.0
varpi_wt_plus	4,6	1.0
varpi_wt_plus	5,6	1.0
varpi_wt_plus	1,7	1.0
varpi_wt_plus	2,7	1.0
varpi_wt_plus	3,7	1.0
varpi_wt_plus	4,7	1.0
varpi_wt_plus	5,7	1.0
varpi_wt_plus	1,8	1.0
varpi_wt_plus	2,8	1.0
varpi_wt_plus	3,8	1.0
varpi_wt_plus	4,8	1.0
varpi_wt_plus	5,8	1.0
varpi_wt_plus	1,9	1.0
varpi_wt_plus	2,9	1.0
varpi_wt_plus	3,9	1.0
varpi_wt_plus	4,9	1.0
varpi_wt_plus	5,9	1.0
varpi_wt_plus	1,10	1.0
varpi_wt_plus	2,10	1.0
varpi_wt_plus	3,10	1.0
varpi_wt_plus	4,10	1.0
varpi_wt_plus	5,10	1.0
varpi_wt_plus	1,11	1.0
varpi_wt_plus	2,11	1.0
varpi_wt_plus	3,11	1.0
varpi_wt_plus	4,11	1.0
varpi_wt_plus	5,11	1.0
varpi_wt_plus	1,12	1.0
varpi_wt_plus	2,12	1.0
varpi_wt_plus	3,12	1.0
varpi_wt_plus	4,12	1.0
varpi_wt_plus	5,12	1.0
varpi_wt_plus	1,13	1.0
varpi_wt_plus	2,13	1.0
varpi_wt_plus	3,13	1.0
varpi_wt_plus	4,13	1.0
varpi_wt_plus	5,13	1.0
varpi_wt_plus	1,14	1.0
varpi_wt_plus	2,14	1.0
varpi_wt_plus	3,14	1.0
varpi_wt_plus	4,14	1.0
varpi_wt_plus	5,14	1.0
varpi_wt_plus	1,15	1.0
varpi_wt_plus	2,15	1.0
varpi_wt_plus	3,15	1.0
varpi_wt_plus	4,15	1.0
varpi_wt_plus	5,15	1.0
varpi_wt_plus	1,16	1.0
varpi_wt_plus	2,16	1.0
varpi_wt_plus	3,16	1.0
varpi_wt_plus	4,16	1.0
varpi_wt_plus	5,16	1.0
varpi_wt_plus	1,17	1.0
varpi_wt_plus	2,17	1.0
varpi_wt_plus	3,17	1.0
varpi_wt_plus	4,17	1.0
varpi_wt_plus	5,17	1.0
varpi_wt_plus	1,18	1.0
varpi_wt_plus	2,18	1.0
varpi_wt_plus	3,18	1.0
varpi_wt_plus	4,18	1.0
varpi_wt_plus	5,18	1.0
varpi_wt_plus	1,19	1.0
varpi_wt_plus	2,19	1.0
varpi_wt_plus	3,19	1.0
varpi_wt_plus	4,19	1.0
varpi_wt_plus	5,19	1.0
varpi_wt_plus	1,20	1.0
varpi_wt_plus	2,20	1.0
varpi_wt_plus	3,20	1.0
varpi_wt_plus	4,20	1.0
varpi_wt_plus	5,20	1.0
varpi_wt_plus	1,21	1.0
varpi_wt_plus	2,21	1.0
varpi_wt_plus	3,21	1.0
varpi_wt_plus	4,21	1.0
varpi_wt_plus	5,21	1.0
varpi_wt_plus	1,22	1.0
varpi_wt_plus	2,22	1.0
varpi_wt_plus	3,22	1.0
varpi_wt_plus	4,22	1.0
varpi_wt_plus	5,22	1.0
varpi_wt_plus	1,23	1.0
varpi_wt_plus	2,23	1.0
varpi_wt_plus	3,23	1.0
varpi_wt_plus	4,23	1.0
varpi_wt_plus	5,23	1.0
varpi_wt_plus	1,24	1.0
varpi_wt_plus	2,24	1.0
varpi_wt_plus	3,24	1.0
varpi_wt_plus	4,24	1.0
varpi_wt_plus	5,24	1.0
varpi_wt_plus	1,25	1.0
varpi_wt_plus	2,25	1.0
varpi_wt_plus	3,25	1.0
varpi_wt_plus	4,25	1.0
varpi_wt_plus	5,25	1.0
varpi_wt_plus	1,26	1.0
varpi_wt_plus	2,26	1.0
varpi_wt_plus	3,26	1.0
varpi_wt_plus	4,26	1.0
varpi_wt_plus	5,26	1.0
varpi_wt_plus	1,27	1.0
varpi_wt_plus	2,27	1.0
varpi_wt_plus	3,27	1.0
varpi_wt_plus	4,27	1.0
varpi_wt_plus	5,27	1.0
varpi_wt_plus	1,28	1.0
varpi_wt_plus	2,28	1.0
varpi_wt_plus	3,28	1.0
varpi_wt_plus	4,28	1.0
varpi_wt_plus	5,28	1.0
varpi_wt_plus	1,29	1.0
varpi_wt_plus	2,29	1.0
varpi_wt_plus	3,29	1.0
varpi_wt_plus	4,29	1.0
varpi_wt_plus	5,29	1.0
varpi_wt_plus	1,30	1.0
varpi_wt_plus	2,30	1.0
varpi_wt_plus	3,30	1.0
varpi_wt_plus	4,30	1.0
varpi_wt_plus	5,30	1.0
varpi_wt_plus	1,31	1.0
varpi_wt_plus	2,31	1.0
varpi_wt_plus	3,31	1.0
varpi_wt_plus	4,31	1.0
varpi_wt_plus	5,31	1.0
varpi_wt_plus	1,32	1.0
varpi_wt_plus	2,32	1.0
varpi_wt_plus	3,32	1.0
varpi_wt_plus	4,32	1.0
varpi_wt_plus	5,32	1.0
varpi_wt_plus	1,33	1.0
varpi_wt_plus	2,33	1.0
varpi_wt_plus	3,33	1.0
varpi_wt_plus	4,33	1.0
varpi_wt_plus	5,33	1.0
varpi_wt_plus	1,34	1.0
varpi_wt_plus	2,34	1.0
varpi_wt_plus	3,34	1.0
varpi_wt_plus	4,34	1.0
varpi_wt_plus	5,34	1.0
varpi_wt_plus	1,35	1.0
varpi_wt_plus	2,35	1.0
varpi_wt_plus	3,35	1.0
varpi_wt_plus	4,35	1.0
varpi_wt_plus	5,35	1.0
varpi_wt_plus	1,36	1.0
varpi_wt_plus	2,36	1.0
varpi_wt_plus	3,36	1.0
varpi_wt_plus	4,36	1.0
varpi_wt_plus	5,36	1.0
varpi_wt_plus	1,37	1.0
varpi_wt_plus	2,37	1.0
varpi_wt_plus	3,37	1.0
varpi_wt_plus	4,37	1.0
varpi_wt_plus	5,37	1.0
varpi_wt_plus	1,38	1.0
varpi_wt_plus	2,38	1.0
varpi_wt_plus	3,38	1.0
varpi_wt_plus	4,38	1.0
varpi_wt_plus	5,38	1.0
varpi_wt_plus	1,39	1.0
varpi_wt_plus	2,39	1.0
varpi_wt_plus	3,39	1.0
varpi_wt_plus	4,39	1.0
varpi_wt_plus	5,39	1.0
varpi_wt_plus	1,40	1.0
varpi_wt_plus	2,40	1.0
varpi_wt_plus	3,40	1.0
varpi_wt_plus	4,40	1.0
varpi_wt_plus	5,40	1.0
varpi_wt_plus	1,41	1.0
varpi_wt_plus	2,41	1.0
varpi_wt_plus	3,41	1.0
varpi_wt_plus	4,41	1.0
varpi_wt_plus	5,41	1.0
varpi_wt_plus	1,42	1.0
varpi_wt_plus	2,42	1.0
varpi_wt_plus	3,42	1.0
varpi_wt_plus	4,42	1.0
varpi_wt_plus	5,42	1.0
varpi_wt_plus	1,43	1.0
varpi_wt_plus	2,43	1.0
varpi_wt_plus	3,43	1.0
varpi_wt_plus	4,43	1.0
varpi_wt_plus	5,43	1.0
varpi_wt_plus	1,44	1.0
varpi_wt_plus	2,44	1.0
varpi_wt_plus	3,44	1.0
varpi_wt_plus	4,44	1.0
varpi_wt_plus	5,44	1.0
varpi_wt_plus	1,45	1.0
varpi_wt_plus	2,45	1.0
varpi_wt_plus	3,45	1.0
varpi_wt_plus	4,45	1.0
varpi_wt_plus	5,45	1.0
varpi_wt_plus	1,46	1.0
varpi_wt_plus	2,46	1.0
varpi_wt_plus	3,46	1.0
varpi_wt_plus	4,46	1.0
varpi_wt_plus	5,46	1.0
varpi_wt_plus	1,47	1.0
varpi_wt_plus	2,47	1.0
varpi_wt_plus	3,47	1.0
varpi_wt_plus	4,47	1.0
varpi_wt_plus	5,47	1.0
varpi_wt_plus	1,48	1.0
varpi_wt_plus	2,48	1.0
varpi_wt_plus	3,48	1.0
varpi_wt_plus	4,48	1.0
varpi_wt_plus	5,48	1.0
varpi_wt_plus	1,49	1.0
varpi_wt_plus	2,49	1.0
varpi_wt_plus	3,49	1.0
varpi_wt_plus	4,49	1.0
varpi_wt_plus	5,49	1.0
varpi_wt_plus	1,50	1.0
varpi_wt_plus	2,50	1.0
varpi_wt_plus	3,50	1.0
varpi_wt_plus	4,50	1.0
varpi_wt_plus	5,50	1.0
varpi_wt_plus	1,51	1.0
varpi_wt_plus	2,51	1.0
varpi_wt_plus	3,51	1.0
varpi_wt_plus	4,51	1.0
varpi_wt_plus	5,51	1.0
varpi_wt_plus	1,52	1.0
varpi_wt_plus	2,52	1.0
varpi_wt_plus	3,52	1.0
varpi_wt_plus	4,52	1.0
varpi_wt_plus	5,52	1.0
varpi_wt_plus	1,53	1.0
varpi_wt_plus	2,53	1.0
varpi_wt_plus	3,53	1.0
varpi_wt_plus	4,53	1.0
varpi_wt_plus	5,53	1.0
varpi_wt_plus	1,54	1.0
varpi_wt_plus	2,54	1.0
varpi_wt_plus	3,54	1.0
varpi_wt_plus	4,54	1.0
varpi_wt_plus	5,54	1.0
varpi_wt_plus	1,55	1.0
varpi_wt_plus	2,55	1.0
varpi_wt_plus	3,55	1.0
varpi_wt_plus	4,55	1.0
varpi_wt_plus	5,55	1.0
varpi_wt_plus	1,56	1.0
varpi_wt_plus	2,56	1.0
varpi_wt_plus	3,56	1.0
varpi_wt_plus	4,56	1.0
varpi_wt_plus	5,56	1.0
varpi_wt_plus	1,57	1.0
varpi_wt_plus	2,57	1.0
varpi_wt_plus	3,57	1.0
varpi_wt_plus	4,57	1.0
varpi_wt_plus	5,57	1.0
varpi_wt_plus	1,58	1.0
varpi_wt_plus	2,58	1.0
varpi_wt_plus	3,58	1.0
varpi_wt_plus	4,58	1.0
varpi_wt_plus	5,58	1.0
varpi_wt_plus	1,59	1.0
varpi_wt_plus	2,59	1.0
varpi_wt_plus	3,59	1.0
varpi_wt_plus	4,59	1.0
varpi_wt_plus	5,59	1.0
varpi_wt_plus	1,60	1.0
varpi_wt_plus	2,60	1.0
varpi_wt_plus	3,60	1.0
varpi_wt_plus	4,60	1.0
varpi_wt_plus	5,60	1.0
varpi_wt_plus	1,61	1.0
varpi_wt_plus	2,61	1.0
varpi_wt_plus	3,61	1.0
varpi_wt_plus	4,61	1.0
varpi_wt_plus	5,61	1.0
varpi_wt_plus	1,62	1.0
varpi_wt_plus	2,62	1.0
varpi_wt_plus	3,62	1.0
varpi_wt_plus	4,62	1.0
varpi_wt_plus	5,62	1.0
varpi_wt_plus	1,63	1.0
varpi_wt_plus	2,63	1.0
varpi_wt_plus	3,63	1.0
varpi_wt_plus	4,63	1.0
varpi_wt_plus	5,63	1.0
varpi_wt_plus	1,64	1.0
varpi_wt_plus	2,64	1.0
varpi_wt_plus	3,64	1.0
varpi_wt_plus	4,64	1.0
varpi_wt_plus	5,64	1.0
varpi_wt_plus	1,65	1.0
varpi_wt_plus	2,65	1.0
varpi_wt_plus	3,65	1.0
varpi_wt_plus	4,65	1.0
varpi_wt_plus	5,65	1.0
varpi_wt_plus	1,66	1.0
varpi_wt_plus	2,66	1.0
varpi_wt_plus	3,66	1.0
varpi_wt_plus	4,66	1.0
varpi_wt_plus	5,66	1.0
varpi_wt_plus	1,67	1.0
varpi_wt_plus	2,67	1.0
varpi_wt_plus	3,67	1.0
varpi_wt_plus	4,67	1.0
varpi_wt_plus	5,67	1.0
varpi_wt_plus	1,68	1.0
varpi_wt_plus	2,68	1.0
varpi_wt_plus	3,68	1.0
varpi_wt_plus	4,68	1.0
varpi_wt_plus	5,68	1.0
varpi_wt_plus	1,69	1.0
varpi_wt_plus	2,69	1.0
varpi_wt_plus	3,69	1.0
varpi_wt_plus	4,69	1.0
varpi_wt_plus	5,69	1.0
varpi_wt_plus	1,70	1.0
varpi_wt_plus	2,70	1.0
varpi_wt_plus	3,70	1.0
varpi_wt_plus	4,70	1.0
varpi_wt_plus	5,70	1.0
varpi_wt_plus	1,71	1.0
varpi_wt_plus	2,71	1.0
varpi_wt_plus	3,71	1.0
varpi_wt_plus	4,71	1.0
varpi_wt_plus	5,71	1.0
varpi_wt_plus	1,72	1.0
varpi_wt_plus	2,72	1.0
varpi_wt_plus	3,72	1.0
varpi_wt_plus	4,72	1.0
varpi_wt_plus	5,72	1.0
varpi_wt_plus	1,73	1.0
varpi_wt_plus	2,73	1.0
varpi_wt_plus	3,73	1.0
varpi_wt_plus	4,73	1.0
varpi_wt_plus	5,73	1.0
varpi_wt_plus	1,74	1.0
varpi_wt_plus	2,74	1.0
varpi_wt_plus	3,74	1.0
varpi_wt_plus	4,74	1.0
varpi_wt_plus	5,74	1.0
varpi_wt_plus	1,75	1.0
varpi_wt_plus	2,75	1.0
varpi_wt_plus	3,75	1.0
varpi_wt_plus	4,75	1.0
varpi_wt_plus	5,75	1.0
varpi_wt_plus	1,76	1.0
varpi_wt_plus	2,76	1.0
varpi_wt_plus	3,76	1.0
varpi_wt_plus	4,76	1.0
varpi_wt_plus	5,76	1.0
varpi_wt_plus	1,77	1.0
varpi_wt_plus	2,77	1.0
varpi_wt_plus	3,77	1.0
varpi_wt_plus	4,77	1.0
varpi_wt_plus	5,77	1.0
varpi_wt_plus	1,78	1.0
varpi_wt_plus	2,78	1.0
varpi_wt_plus	3,78	1.0
varpi_wt_plus	4,78	1.0
varpi_wt_plus	5,78	1.0
varpi_wt_plus	1,79	1.0
varpi_wt_plus	2,79	1.0
varpi_wt_plus	3,79	1.0
varpi_wt_plus	4,79	1.0
varpi_wt_plus	5,79	1.0
varpi_wt_plus	1,80	1.0
varpi_wt_plus	2,80	1.0
varpi_wt_plus	3,80	1.0
varpi_wt_plus	4,80	1.0
varpi_wt_plus	5,80	1.0
varpi_wt_plus	1,81	1.0
varpi_wt_plus	2,81	1.0
varpi_wt_plus	3,81	1.0
varpi_wt_plus	4,81	1.0
varpi_wt_plus	5,81	1.0
varpi_wt_plus	1,82	1.0
varpi_wt_plus	2,82	1.0
varpi_wt_plus	3,82	1.0
varpi_wt_plus	4,82	1.0
varpi_wt_plus	5,82	1.0
varpi_wt_plus	1,83	1.0
varpi_wt_plus	2,83	1.0
varpi_wt_plus	3,83	1.0
varpi_wt_plus	4,83	1.0
varpi_wt_plus	5,83	1.0
varpi_wt_plus	1,84	1.0
varpi_wt_plus	2,84	1.0
varpi_wt_plus	3,84	1.0
varpi_wt_plus	4,84	1.0
varpi_wt_plus	5,84	1.0
varpi_wt_plus	1,85	1.0
varpi_wt_plus	2,85	1.0
varpi_wt_plus	3,85	1.0
varpi_wt_plus	4,85	1.0
varpi_wt_plus	5,85	1.0
varpi_wt_plus	1,86	1.0
varpi_wt_plus	2,86	1.0
varpi_wt_plus	3,86	1.0
varpi_wt_plus	4,86	1.0
varpi_wt_plus	5,86	1.0
varpi_wt_plus	1,87	1.0
varpi_wt_plus	2,87	1.0
varpi_wt_plus	3,87	1.0
varpi_wt_plus	4,87	1.0
varpi_wt_plus	5,87	1.0
varpi_wt_plus	1,88	1.0
varpi_wt_plus	2,88	1.0
varpi_wt_plus	3,88	1.0
varpi_wt_plus	4,88	1.0
varpi_wt_plus	5,88	1.0
varpi_wt_plus	1,89	1.0
varpi_wt_plus	2,89	1.0
varpi_wt_plus	3,89	1.0
varpi_wt_plus	4,89	1.0
varpi_wt_plus	5,89	1.0
varpi_wt_plus	1,90	1.0
varpi_wt_plus	2,90	1.0
varpi_wt_plus	3,90	1.0
varpi_wt_plus	4,90	1.0
varpi_wt_plus	5,90	1.0
varpi_wt_plus	1,91	1.0
varpi_wt_plus	2,91	1.0
varpi_wt_plus	3,91	1.0
varpi_wt_plus	4,91	1.0
varpi_wt_plus	5,91	1.0
varpi_wt_plus	1,92	1.0
varpi_wt_plus	2,92	1.0
varpi_wt_plus	3,92	1.0
varpi_wt_plus	4,92	1.0
varpi_wt_plus	5,92	1.0
varpi_wt_plus	1,93	1.0
varpi_wt_plus	2,93	1.0
varpi_wt_plus	3,93	1.0
varpi_wt_plus	4,93	1.0
varpi_wt_plus	5,93	1.0
varpi_wt_plus	1,94	1.0
varpi_wt_plus	2,94	1.0
varpi_wt_plus	3,94	1.0
varpi_wt_plus	4,94	1.0
varpi_wt_plus	5,94	1.0
varpi_wt_plus	1,95	1.0
varpi_wt_plus	2,95	1.0
varpi_wt_plus	3,95	1.0
varpi_wt_plus	4,95	1.0
varpi_wt_plus	5,95	1.0
varpi_wt_plus	1,96	1.0
varpi_wt_plus	2,96	1.0
varpi_wt_plus	3,96	1.0
varpi_wt_plus	4,96	1.0
varpi_wt_plus	5,96	1.0
xi_wt	1,1	1.0735000000000001
xi_wt	2,1	1.0735000000000001
xi_wt	3,1	1.0735000000000001
xi_wt	4,1	1.0735000000000001
xi_wt	5,1	1.0735000000000001
xi_wt	1,2	1.05725
xi_wt	2,2	1.05725
xi_wt	3,2	1.05725
xi_wt	4,2	1.05725
xi_wt	5,2	1.05725
xi_wt	1,3	0.9904999999999999
xi_wt	2,3	0.9904999999999999
xi_wt	3,3	0.9904999999999999
xi_wt	4,3	0.9904999999999999
xi_wt	5,3	0.9904999999999999
xi_wt	1,4	0.825125
xi_wt	2,4	0.825125
xi_wt	3,4	0.825125
xi_wt	4,4	0.825125
xi_wt	5,4	0.825125
xi_wt	1,5	0.751125
xi_wt	2,5	0.751125
xi_wt	3,5	0.751125
xi_wt	4,5	0.751125
xi_wt	5,5	0.751125
xi_wt	1,6	0.9808749999999999
xi_wt	2,6	0.9808749999999999
xi_wt	3,6	0.9808749999999999
xi_wt	4,6	0.9808749999999999
xi_wt	5,6	0.9808749999999999
xi_wt	1,7	0.7655000000000001
xi_wt	2,7	0.7655000000000001
xi_wt	3,7	0.7655000000000001
xi_wt	4,7	0.7655000000000001
xi_wt	5,7	0.7655000000000001
xi_wt	1,8	0.862
xi_wt	2,8	0.862
xi_wt	3,8	0.862
xi_wt	4,8	0.862
xi_wt	5,8	0.862
xi_wt	1,9	0.674125
xi_wt	2,9	0.674125
xi_wt	3,9	0.674125
xi_wt	4,9	0.674125
xi_wt	5,9	0.674125
xi_wt	1,10	0.763625
xi_wt	2,10	0.763625
xi_wt	3,10	0.763625
xi_wt	4,10	0.763625
xi_wt	5,10	0.763625
xi_wt	1,11	0.568375
xi_wt	2,11	0.568375
xi_wt	3,11	0.568375
xi_wt	4,11	0.568375
xi_wt	5,11	0.568375
xi_wt	1,12	0.5405
xi_wt	2,12	0.5405
xi_wt	3,12	0.5405
xi_wt	4,12	0.5405
xi_wt	5,12	0.5405
xi_wt	1,13	0.6256249999999999
xi_wt	2,13	0.6256249999999999
xi_wt	3,13	0.6256249999999999
xi_wt	4,13	0.6256249999999999
xi_wt	5,13	0.6256249999999999
xi_wt	1,14	0.5543750000000001
xi_wt	2,14	0.5543750000000001
xi_wt	3,14	0.5543750000000001
xi_wt	4,14	0.5543750000000001
xi_wt	5,14	0.5543750000000001
xi_wt	1,15	0.5876250000000001
xi_wt	2,15	0.5876250000000001
xi_wt	3,15	0.5876250000000001
xi_wt	4,15	0.5876250000000001
xi_wt	5,15	0.5876250000000001
xi_wt	1,16	0.624
xi_wt	2,16	0.624
xi_wt	3,16	0.624
xi_wt	4,16	0.624
xi_wt	5,16	0.624
xi_wt	1,17	0.67625
xi_wt	2,17	0.67625
xi_wt	3,17	0.67625
xi_wt	4,17	0.67625
xi_wt	5,17	0.67625
xi_wt	1,18	0.5920000000000001
xi_wt	2,18	0.5920000000000001
xi_wt	3,18	0.5920000000000001
xi_wt	4,18	0.5920000000000001
xi_wt	5,18	0.5920000000000001
xi_wt	1,19	0.8165
xi_wt	2,19	0.8165
xi_wt	3,19	0.8165
xi_wt	4,19	0.8165
xi_wt	5,19	0.8165
xi_wt	1,20	0.925875
xi_wt	2,20	0.925875
xi_wt	3,20	0.925875
xi_wt	4,20	0.925875
xi_wt	5,20	0.925875
xi_wt	1,21	0.943625
xi_wt	2,21	0.943625
xi_wt	3,21	0.943625
xi_wt	4,21	0.943625
xi_wt	5,21	0.943625
xi_wt	1,22	0.96675
xi_wt	2,22	0.96675
xi_wt	3,22	0.96675
xi_wt	4,22	0.96675
xi_wt	5,22	0.96675
xi_wt	1,23	1.05175
xi_wt	2,23	1.05175
xi_wt	3,23	1.05175
xi_wt	4,23	1.05175
xi_wt	5,23	1.05175
xi_wt	1,24	0.8699999999999999
xi_wt	2,24	0.8699999999999999
xi_wt	3,24	0.8699999999999999
xi_wt	4,24	0.8699999999999999
xi_wt	5,24	0.8699999999999999
xi_wt	1,25	1.065
xi_wt	2,25	1.065
xi_wt	3,25	1.065
xi_wt	4,25	1.065
xi_wt	5,25	1.065
xi_wt	1,26	1.047625
xi_wt	2,26	1.047625
xi_wt	3,26	1.047625
xi_wt	4,26	1.047625
xi_wt	5,26	1.047625
xi_wt	1,27	1.119625
xi_wt	2,27	1.119625
xi_wt	3,27	1.119625
xi_wt	4,27	1.119625
xi_wt	5,27	1.119625
xi_wt	1,28	0.838
xi_wt	2,28	0.838
xi_wt	3,28	0.838
xi_wt	4,28	0.838
xi_wt	5,28	0.838
xi_wt	1,29	0.81675
xi_wt	2,29	0.81675
xi_wt	3,29	0.81675
xi_wt	4,29	0.81675
xi_wt	5,29	0.81675
xi_wt	1,30	0.892
xi_wt	2,30	0.892
xi_wt	3,30	0.892
xi_wt	4,30	0.892
xi_wt	5,30	0.892
xi_wt	1,31	0.80525
xi_wt	2,31	0.80525
xi_wt	3,31	0.80525
xi_wt	4,31	0.80525
xi_wt	5,31	0.80525
xi_wt	1,32	0.7340000000000001
xi_wt	2,32	0.7340000000000001
xi_wt	3,32	0.7340000000000001
xi_wt	4,32	0.7340000000000001
xi_wt	5,32	0.7340000000000001
xi_wt	1,33	0.657875
xi_wt	2,33	0.657875
xi_wt	3,33	0.657875
xi_wt	4,33	0.657875
xi_wt	5,33	0.657875
xi_wt	1,34	0.659
xi_wt	2,34	0.659
xi_wt	3,34	0.659
xi_wt	4,34	0.659
xi_wt	5,34	0.659
xi_wt	1,35	0.556875
xi_wt	2,35	0.556875
xi_wt	3,35	0.556875
xi_wt	4,35	0.556875
xi_wt	5,35	0.556875
xi_wt	1,36	0.477
xi_wt	2,36	0.477
xi_wt	3,36	0.477
xi_wt	4,36	0.477
xi_wt	5,36	0.477
xi_wt	1,37	0.6265
xi_wt	2,37	0.6265
xi_wt	3,37	0.6265
xi_wt	4,37	0.6265
xi_wt	5,37	0.6265
xi_wt	1,38	0.55575
xi_wt	2,38	0.55575
xi_wt	3,38	0.55575
xi_wt	4,38	0.55575
xi_wt	5,38	0.55575
xi_wt	1,39	0.5825
xi_wt	2,39	0.5825
xi_wt	3,39	0.5825
xi_wt	4,39	0.5825
xi_wt	5,39	0.5825
xi_wt	1,40	0.59075
xi_wt	2,40	0.59075
xi_wt	3,40	0.59075
xi_wt	4,40	0.59075
xi_wt	5,40	0.59075
xi_wt	1,41	0.6408750000000001
xi_wt	2,41	0.6408750000000001
xi_wt	3,41	0.6408750000000001
xi_wt	4,41	0.6408750000000001
xi_wt	5,41	0.6408750000000001
xi_wt	1,42	0.654625
xi_wt	2,42	0.654625
xi_wt	3,42	0.654625
xi_wt	4,42	0.654625
xi_wt	5,42	0.654625
xi_wt	1,43	0.864875
xi_wt	2,43	0.864875
xi_wt	3,43	0.864875
xi_wt	4,43	0.864875
xi_wt	5,43	0.864875
xi_wt	1,44	0.979625
xi_wt	2,44	0.979625
xi_wt	3,44	0.979625
xi_wt	4,44	0.979625
xi_wt	5,44	0.979625
xi_wt	1,45	0.9041250000000001
xi_wt	2,45	0.9041250000000001
xi_wt	3,45	0.9041250000000001
xi_wt	4,45	0.9041250000000001
xi_wt	5,45	0.9041250000000001
xi_wt	1,46	0.9005000000000001
xi_wt	2,46	0.9005000000000001
xi_wt	3,46	0.9005000000000001
xi_wt	4,46	0.9005000000000001
xi_wt	5,46	0.9005000000000001
xi_wt	1,47	0.9568749999999999
xi_wt	2,47	0.9568749999999999
xi_wt	3,47	0.9568749999999999
xi_wt	4,47	0.9568749999999999
xi_wt	5,47	0.9568749999999999
xi_wt	1,48	0.9205000000000001
xi_wt	2,48	0.9205000000000001
xi_wt	3,48	0.9205000000000001
xi_wt	4,48	0.9205000000000001
xi_wt	5,48	0.9205000000000001
xi_wt	1,49	1.060125
xi_wt	2,49	1.060125
xi_wt	3,49	1.060125
xi_wt	4,49	1.060125
xi_wt	5,49	1.060125
xi_wt	1,50	1.0465
xi_wt	2,50	1.0465
xi_wt	3,50	1.0465
xi_wt	4,50	1.0465
xi_wt	5,50	1.0465
xi_wt	1,51	1.06525
xi_wt	2,51	1.06525
xi_wt	3,51	1.06525
xi_wt	4,51	1.06525
xi_wt	5,51	1.06525
xi_wt	1,52	0.923625
xi_wt	2,52	0.923625
xi_wt	3,52	0.923625
xi_wt	4,52	0.923625
xi_wt	5,52	0.923625
xi_wt	1,53	0.827625
xi_wt	2,53	0.827625
xi_wt	3,53	0.827625
xi_wt	4,53	0.827625
xi_wt	5,53	0.827625
xi_wt	1,54	1.072125
xi_wt	2,54	1.072125
xi_wt	3,54	1.072125
xi_wt	4,54	1.072125
xi_wt	5,54	1.072125
xi_wt	1,55	0.750875
xi_wt	2,55	0.750875
xi_wt	3,55	0.750875
xi_wt	4,55	0.750875
xi_wt	5,55	0.750875
xi_wt	1,56	0.84075
xi_wt	2,56	0.84075
xi_wt	3,56	0.84075
xi_wt	4,56	0.84075
xi_wt	5,56	0.84075
xi_wt	1,57	0.7455
xi_wt	2,57	0.7455
xi_wt	3,57	0.7455
xi_wt	4,57	0.7455
xi_wt	5,57	0.7455
xi_wt	1,58	0.6675
xi_wt	2,58	0.6675
xi_wt	3,58	0.6675
xi_wt	4,58	0.6675
xi_wt	5,58	0.6675
xi_wt	1,59	0.671625
xi_wt	2,59	0.671625
xi_wt	3,59	0.671625
xi_wt	4,59	0.671625
xi_wt	5,59	0.671625
xi_wt	1,60	0.55525
xi_wt	2,60	0.55525
xi_wt	3,60	0.55525
xi_wt	4,60	0.55525
xi_wt	5,60	0.55525
xi_wt	1,61	0.6165
xi_wt	2,61	0.6165
xi_wt	3,61	0.6165
xi_wt	4,61	0.6165
xi_wt	5,61	0.6165
xi_wt	1,62	0.533875
xi_wt	2,62	0.533875
xi_wt	3,62	0.533875
xi_wt	4,62	0.533875
xi_wt	5,62	0.533875
xi_wt	1,63	0.508
xi_wt	2,63	0.508
xi_wt	3,63	0.508
xi_wt	4,63	0.508
xi_wt	5,63	0.508
xi_wt	1,64	0.567875
xi_wt	2,64	0.567875
xi_wt	3,64	0.567875
xi_wt	4,64	0.567875
xi_wt	5,64	0.567875
xi_wt	1,65	0.65125
xi_wt	2,65	0.65125
xi_wt	3,65	0.65125
xi_wt	4,65	0.65125
xi_wt	5,65	0.65125
xi_wt	1,66	0.53225
xi_wt	2,66	0.53225
xi_wt	3,66	0.53225
xi_wt	4,66	0.53225
xi_wt	5,66	0.53225
xi_wt	1,67	0.8692500000000001
xi_wt	2,67	0.8692500000000001
xi_wt	3,67	0.8692500000000001
xi_wt	4,67	0.8692500000000001
xi_wt	5,67	0.8692500000000001
xi_wt	1,68	0.928875
xi_wt	2,68	0.928875
xi_wt	3,68	0.928875
xi_wt	4,68	0.928875
xi_wt	5,68	0.928875
xi_wt	1,69	0.8878750000000001
xi_wt	2,69	0.8878750000000001
xi_wt	3,69	0.8878750000000001
xi_wt	4,69	0.8878750000000001
xi_wt	5,69	0.8878750000000001
xi_wt	1,70	0.907125
xi_wt	2,70	0.907125
xi_wt	3,70	0.907125
xi_wt	4,70	0.907125
xi_wt	5,70	0.907125
xi_wt	1,71	1.14275
xi_wt	2,71	1.14275
xi_wt	3,71	1.14275
xi_wt	4,71	1.14275
xi_wt	5,71	1.14275
xi_wt	1,72	0.9385
xi_wt	2,72	0.9385
xi_wt	3,72	0.9385
xi_wt	4,72	0.9385
xi_wt	5,72	0.9385
xi_wt	1,73	1.056
xi_wt	2,73	1.056
xi_wt	3,73	1.056
xi_wt	4,73	1.056
xi_wt	5,73	1.056
xi_wt	1,74	1.25
xi_wt	2,74	1.25
xi_wt	3,74	1.25
xi_wt	4,74	1.25
xi_wt	5,74	1.25
xi_wt	1,75	1.110875
xi_wt	2,75	1.110875
xi_wt	3,75	1.110875
xi_wt	4,75	1.110875
xi_wt	5,75	1.110875
xi_wt	1,76	0.71975
xi_wt	2,76	0.71975
xi_wt	3,76	0.71975
xi_wt	4,76	0.71975
xi_wt	5,76	0.71975
xi_wt	1,77	0.711
xi_wt	2,77	0.711
xi_wt	3,77	0.711
xi_wt	4,77	0.711
xi_wt	5,77	0.711
xi_wt	1,78	0.7918749999999999
xi_wt	2,78	0.7918749999999999
xi_wt	3,78	0.7918749999999999
xi_wt	4,78	0.7918749999999999
xi_wt	5,78	0.7918749999999999
xi_wt	1,79	0.853875
xi_wt	2,79	0.853875
xi_wt	3,79	0.853875
xi_wt	4,79	0.853875
xi_wt	5,79	0.853875
xi_wt	1,80	0.900625
xi_wt	2,80	0.900625
xi_wt	3,80	0.900625
xi_wt	4,80	0.900625
xi_wt	5,80	0.900625
xi_wt	1,81	0.7395
xi_wt	2,81	0.7395
xi_wt	3,81	0.7395
xi_wt	4,81	0.7395
xi_wt	5,81	0.7395
xi_wt	1,82	0.680625
xi_wt	2,82	0.680625
xi_wt	3,82	0.680625
xi_wt	4,82	0.680625
xi_wt	5,82	0.680625
xi_wt	1,83	0.586625
xi_wt	2,83	0.586625
xi_wt	3,83	0.586625
xi_wt	4,83	0.586625
xi_wt	5,83	0.586625
xi_wt	1,84	0.581875
xi_wt	2,84	0.581875
xi_wt	3,84	0.581875
xi_wt	4,84	0.581875
xi_wt	5,84	0.581875
xi_wt	1,85	0.610375
xi_wt	2,85	0.610375
xi_wt	3,85	0.610375
xi_wt	4,85	0.610375
xi_wt	5,85	0.610375
xi_wt	1,86	0.519875
xi_wt	2,86	0.519875
xi_wt	3,86	0.519875
xi_wt	4,86	0.519875
xi_wt	5,86	0.519875
xi_wt	1,87	0.5605
xi_wt	2,87	0.5605
xi_wt	3,87	0.5605
xi_wt	4,87	0.5605
xi_wt	5,87	0.5605
xi_wt	1,88	0.649
xi_wt	2,88	0.649
xi_wt	3,88	0.649
xi_wt	4,88	0.649
xi_wt	5,88	0.649
xi_wt	1,89	0.572625
xi_wt	2,89	0.572625
xi_wt	3,89	0.572625
xi_wt	4,89	0.572625
xi_wt	5,89	0.572625
xi_wt	1,90	0.57525
xi_wt	2,90	0.57525
xi_wt	3,90	0.57525
xi_wt	4,90	0.57525
xi_wt	5,90	0.57525
xi_wt	1,91	0.732375
xi_wt	2,91	0.732375
xi_wt	3,91	0.732375
xi_wt	4,91	0.732375
xi_wt	5,91	0.732375
xi_wt	1,92	0.87625
xi_wt	2,92	0.87625
xi_wt	3,92	0.87625
xi_wt	4,92	0.87625
xi_wt	5,92	0.87625
xi_wt	1,93	0.84825
xi_wt	2,93	0.84825
xi_wt	3,93	0.84825
xi_wt	4,93	0.84825
xi_wt	5,93	0.84825
xi_wt	1,94	0.8765000000000001
xi_wt	2,94	0.8765000000000001
xi_wt	3,94	0.8765000000000001
xi_wt	4,94	0.8765000000000001
xi_wt	5,94	0.8765000000000001
xi_wt	1,95	1.033625
xi_wt	2,95	1.033625
xi_wt	3,95	1.033625
xi_wt	4,95	1.033625
xi_wt	5,95	1.033625
xi_wt	1,96	0.76175
xi_wt	2,96	0.76175
xi_wt	3,96	0.76175
xi_wt	4,96	0.76175
xi_wt	5,96	0.76175
zeta_pv	1,1	0.0
zeta_pv	2,1	0.0
zeta_pv	3,1	0.0
zeta_pv	4,1	0.0
zeta_pv	5,1	0.0
zeta_pv	1,2	0.0
zeta_pv	2,2	0.0
zeta_pv	3,2	0.0
zeta_pv	4,2	0.0
zeta_pv	5,2	0.0
zeta_pv	1,3	0.0
zeta_pv	2,3	0.0
zeta_pv	3,3	0.0
zeta_pv	4,3	0.0
zeta_pv	5,3	0.0
zeta_pv	1,4	0.0
zeta_pv	2,4	0.0
zeta_pv	3,4	0.0
zeta_pv	4,4	0.0
zeta_pv	5,4	0.0
zeta_pv	1,5	0.0
zeta_pv	2,5	0.0
zeta_pv	3,5	0.0
zeta_pv	4,5	0.0
zeta_pv	5,5	0.0
zeta_pv	1,6	0.0
zeta_pv	2,6	0.0
zeta_pv	3,6	0.0
zeta_pv	4,6	0.0
zeta_pv	5,6	0.0
zeta_pv	1,7	0.16445
zeta_pv	2,7	0.16445
zeta_pv	3,7	0.16445
zeta_pv	4,7	0.16445
zeta_pv	5,7	0.16445
zeta_pv	1,8	0.49929000000000007
zeta_pv	2,8	0.49929000000000007
zeta_pv	3,8	0.49929000000000007
zeta_pv	4,8	0.49929000000000007
zeta_pv	5,8	0.49929000000000007
zeta_pv	1,9	0.87736
zeta_pv	2,9	0.87736
zeta_pv	3,9	0.87736
zeta_pv	4,9	0.87736
zeta_pv	5,9	0.87736
zeta_pv	1,10	0.9201500000000001
zeta_pv	2,10	0.9201500000000001
zeta_pv	3,10	0.9201500000000001
zeta_pv	4,10	0.9201500000000001
zeta_pv	5,10	0.9201500000000001
zeta_pv	1,11	0.9201500000000001
zeta_pv	2,11	0.9201500000000001
zeta_pv	3,11	0.9201500000000001
zeta_pv	4,11	0.9201500000000001
zeta_pv	5,11	0.9201500000000001
zeta_pv	1,12	0.6439400000000001
zeta_pv	2,12	0.6439400000000001
zeta_pv	3,12	0.6439400000000001
zeta_pv	4,12	0.6439400000000001
zeta_pv	5,12	0.6439400000000001
zeta_pv	1,13	0.6952
zeta_pv	2,13	0.6952
zeta_pv	3,13	0.6952
zeta_pv	4,13	0.6952
zeta_pv	5,13	0.6952
zeta_pv	1,14	0.781
zeta_pv	2,14	0.781
zeta_pv	3,14	0.781
zeta_pv	4,14	0.781
zeta_pv	5,14	0.781
zeta_pv	1,15	1.04786
zeta_pv	2,15	1.04786
zeta_pv	3,15	1.04786
zeta_pv	4,15	1.04786
zeta_pv	5,15	1.04786
zeta_pv	1,16	0.8470000000000001
zeta_pv	2,16	0.8470000000000001
zeta_pv	3,16	0.8470000000000001
zeta_pv	4,16	0.8470000000000001
zeta_pv	5,16	0.8470000000000001
zeta_pv	1,17	0.9542500000000002
zeta_pv	2,17	0.9542500000000002
zeta_pv	3,17	0.9542500000000002
zeta_pv	4,17	0.9542500000000002
zeta_pv	5,17	0.9542500000000002
zeta_pv	1,18	0.88968
zeta_pv	2,18	0.88968
zeta_pv	3,18	0.88968
zeta_pv	4,18	0.88968
zeta_pv	5,18	0.88968
zeta_pv	1,19	0.5668300000000001
zeta_pv	2,19	0.5668300000000001
zeta_pv	3,19	0.5668300000000001
zeta_pv	4,19	0.5668300000000001
zeta_pv	5,19	0.5668300000000001
zeta_pv	1,20	0.38918
zeta_pv	2,20	0.38918
zeta_pv	3,20	0.38918
zeta_pv	4,20	0.38918
zeta_pv	5,20	0.38918
zeta_pv	1,21	0.0
zeta_pv	2,21	0.0
zeta_pv	3,21	0.0
zeta_pv	4,21	0.0
zeta_pv	5,21	0.0
zeta_pv	1,22	0.0
zeta_pv	2,22	0.0
zeta_pv	3,22	0.0
zeta_pv	4,22	0.0
zeta_pv	5,22	0.0
zeta_pv	1,23	0.0
zeta_pv	2,23	0.0
zeta_pv	3,23	0.0
zeta_pv	4,23	0.0
zeta_pv	5,23	0.0
zeta_pv	1,24	0.0
zeta_pv	2,24	0.0
zeta_pv	3,24	0.0
zeta_pv	4,24	0.0
zeta_pv	5,24	0.0
zeta_pv	1,25	0.0
zeta_pv	2,25	0.0
zeta_pv	3,25	0.0
zeta_pv	4,25	0.0
zeta_pv	5,25	0.0
zeta_pv	1,26	0.0
zeta_pv	2,26	0.0
zeta_pv	3,26	0.0
zeta_pv	4,26	0.0
zeta_pv	5,26	0.0
zeta_pv	1,27	0.0
zeta_pv	2,27	0.0
zeta_pv	3,27	0.0
zeta_pv	4,27	0.0
zeta_pv	5,27	0.0
zeta_pv	1,28	0.0
zeta_pv	2,28	0.0
zeta_pv	3,28	0.0
zeta_pv	4,28	0.0
zeta_pv	5,28	0.0
zeta_pv	1,29	0.0
zeta_pv	2,29	0.0
zeta_pv	3,29	0.0
zeta_pv	4,29	0.0
zeta_pv	5,29	0.0
zeta_pv	1,30	0.0
zeta_pv	2,30	0.0
zeta_pv	3,30	0.0
zeta_pv	4,30	0.0
zeta_pv	5,30	0.0
zeta_pv	1,31	0.14399
zeta_pv	2,31	0.14399
zeta_pv	3,31	0.14399
zeta_pv	4,31	0.14399
zeta_pv	5,31	0.14399
zeta_pv	1,32	0.53119
zeta_pv	2,32	0.53119
zeta_pv	3,32	0.53119
zeta_pv	4,32	0.53119
zeta_pv	5,32	0.53119
zeta_pv	1,33	0.8193900000000001
zeta_pv	2,33	0.8193900000000001
zeta_pv	3,33	0.8193900000000001
zeta_pv	4,33	0.8193900000000001
zeta_pv	5,33	0.8193900000000001
zeta_pv	1,34	0.81763
zeta_pv	2,34	0.81763
zeta_pv	3,34	0.81763
zeta_pv	4,34	0.81763
zeta_pv	5,34	0.81763
zeta_pv	1,35	1.0418100000000001
zeta_pv	2,35	1.0418100000000001
zeta_pv	3,35	1.0418100000000001
zeta_pv	4,35	1.0418100000000001
zeta_pv	5,35	1.0418100000000001
zeta_pv	1,36	0.66352
zeta_pv	2,36	0.66352
zeta_pv	3,36	0.66352
zeta_pv	4,36	0.66352
zeta_pv	5,36	0.66352
zeta_pv	1,37	0.67903
zeta_pv	2,37	0.67903
zeta_pv	3,37	0.67903
zeta_pv	4,37	0.67903
zeta_pv	5,37	0.67903
zeta_pv	1,38	0.75438
zeta_pv	2,38	0.75438
zeta_pv	3,38	0.75438
zeta_pv	4,38	0.75438
zeta_pv	5,38	0.75438
zeta_pv	1,39	1.00254
zeta_pv	2,39	1.00254
zeta_pv	3,39	1.00254
zeta_pv	4,39	1.00254
zeta_pv	5,39	1.00254
zeta_pv	1,40	0.9321400000000001
zeta_pv	2,40	0.9321400000000001
zeta_pv	3,40	0.9321400000000001
zeta_pv	4,40	0.9321400000000001
zeta_pv	5,40	0.9321400000000001
zeta_pv	1,41	0.9462200000000001
zeta_pv	2,41	0.9462200000000001
zeta_pv	3,41	0.9462200000000001
zeta_pv	4,41	0.9462200000000001
zeta_pv	5,41	0.9462200000000001
zeta_pv	1,42	0.8115800000000001
zeta_pv	2,42	0.8115800000000001
zeta_pv	3,42	0.8115800000000001
zeta_pv	4,42	0.8115800000000001
zeta_pv	5,42	0.8115800000000001
zeta_pv	1,43	0.6298600000000001
zeta_pv	2,43	0.6298600000000001
zeta_pv	3,43	0.6298600000000001
zeta_pv	4,43	0.6298600000000001
zeta_pv	5,43	0.6298600000000001
zeta_pv	1,44	0.39193000000000006
zeta_pv	2,44	0.39193000000000006
zeta_pv	3,44	0.39193000000000006
zeta_pv	4,44	0.39193000000000006
zeta_pv	5,44	0.39193000000000006
zeta_pv	1,45	0.0
zeta_pv	2,45	0.0
zeta_pv	3,45	0.0
zeta_pv	4,45	0.0
zeta_pv	5,45	0.0
zeta_pv	1,46	0.0
zeta_pv	2,46	0.0
zeta_pv	3,46	0.0
zeta_pv	4,46	0.0
zeta_pv	5,46	0.0
zeta_pv	1,47	0.0
zeta_pv	2,47	0.0
zeta_pv	3,47	0.0
zeta_pv	4,47	0.0
zeta_pv	5,47	0.0
zeta_pv	1,48	0.0
zeta_pv	2,48	0.0
zeta_pv	3,48	0.0
zeta_pv	4,48	0.0
zeta_pv	5,48	0.0
zeta_pv	1,49	0.0
zeta_pv	2,49	0.0
zeta_pv	3,49	0.0
zeta_pv	4,49	0.0
zeta_pv	5,49	0.0
zeta_pv	1,50	0.0
zeta_pv	2,50	0.0
zeta_pv	3,50	0.0
zeta_pv	4,50	0.0
zeta_pv	5,50	0.0
zeta_pv	1,51	0.0
zeta_pv	2,51	0.0
zeta_pv	3,51	0.0
zeta_pv	4,51	0.0
zeta_pv	5,51	0.0
zeta_pv	1,52	0.0
zeta_pv	2,52	0.0
zeta_pv	3,52	0.0
zeta_pv	4,52	0.0
zeta_pv	5,52	0.0
zeta_pv	1,53	0.0
zeta_pv	2,53	0.0
zeta_pv	3,53	0.0
zeta_pv	4,53	0.0
zeta_pv	5,53	0.0
zeta_pv	1,54	0.0
zeta_pv	2,54	0.0
zeta_pv	3,54	0.0
zeta_pv	4,54	0.0
zeta_pv	5,54	0.0
zeta_pv	1,55	0.16995000000000002
zeta_pv	2,55	0.16995000000000002
zeta_pv	3,55	0.16995000000000002
zeta_pv	4,55	0.16995000000000002
zeta_pv	5,55	0.16995000000000002
zeta_pv	1,56	0.5397700000000001
zeta_pv	2,56	0.5397700000000001
zeta_pv	3,56	0.5397700000000001
zeta_pv	4,56	0.5397700000000001
zeta_pv	5,56	0.5397700000000001
zeta_pv	1,57	0.79508
zeta_pv	2,57	0.79508
zeta_pv	3,57	0.79508
zeta_pv	4,57	0.79508
zeta_pv	5,57	0.79508
zeta_pv	1,58	0.9424800000000001
zeta_pv	2,58	0.9424800000000001
zeta_pv	3,58	0.9424800000000001
zeta_pv	4,58	0.9424800000000001
zeta_pv	5,58	0.9424800000000001
zeta_pv	1,59	0.9953900000000001
zeta_pv	2,59	0.9953900000000001
zeta_pv	3,59	0.9953900000000001
zeta_pv	4,59	0.9953900000000001
zeta_pv	5,59	0.9953900000000001
zeta_pv	1,60	0.63811
zeta_pv	2,60	0.63811
zeta_pv	3,60	0.63811
zeta_pv	4,60	0.63811
zeta_pv	5,60	0.63811
zeta_pv	1,61	0.6620900000000001
zeta_pv	2,61	0.6620900000000001
zeta_pv	3,61	0.6620900000000001
zeta_pv	4,61	0.6620900000000001
zeta_pv	5,61	0.6620900000000001
zeta_pv	1,62	0.71313
zeta_pv	2,62	0.71313
zeta_pv	3,62	0.71313
zeta_pv	4,62	0.71313
zeta_pv	5,62	0.71313
zeta_pv	1,63	0.8705400000000001
zeta_pv	2,63	0.8705400000000001
zeta_pv	3,63	0.8705400000000001
zeta_pv	4,63	0.8705400000000001
zeta_pv	5,63	0.8705400000000001
zeta_pv	1,64	0.913
zeta_pv	2,64	0.913
zeta_pv	3,64	0.913
zeta_pv	4,64	0.913
zeta_pv	5,64	0.913
zeta_pv	1,65	0.8869300000000001
zeta_pv	2,65	0.8869300000000001
zeta_pv	3,65	0.8869300000000001
zeta_pv	4,65	0.8869300000000001
zeta_pv	5,65	0.8869300000000001
zeta_pv	1,66	0.9620600000000001
zeta_pv	2,66	0.9620600000000001
zeta_pv	3,66	0.9620600000000001
zeta_pv	4,66	0.9620600000000001
zeta_pv	5,66	0.9620600000000001
zeta_pv	1,67	0.62975
zeta_pv	2,67	0.62975
zeta_pv	3,67	0.62975
zeta_pv	4,67	0.62975
zeta_pv	5,67	0.62975
zeta_pv	1,68	0.40271
zeta_pv	2,68	0.40271
zeta_pv	3,68	0.40271
zeta_pv	4,68	0.40271
zeta_pv	5,68	0.40271
zeta_pv	1,69	0.0
zeta_pv	2,69	0.0
zeta_pv	3,69	0.0
zeta_pv	4,69	0.0
zeta_pv	5,69	0.0
zeta_pv	1,70	0.0
zeta_pv	2,70	0.0
zeta_pv	3,70	0.0
zeta_pv	4,70	0.0
zeta_pv	5,70	0.0
zeta_pv	1,71	0.0
zeta_pv	2,71	0.0
zeta_pv	3,71	0.0
zeta_pv	4,71	0.0
zeta_pv	5,71	0.0
zeta_pv	1,72	0.0
zeta_pv	2,72	0.0
zeta_pv	3,72	0.0
zeta_pv	4,72	0.0
zeta_pv	5,72	0.0
zeta_pv	1,73	0.0
zeta_pv	2,73	0.0
zeta_pv	3,73	0.0
zeta_pv	4,73	0.0
zeta_pv	5,73	0.0
zeta_pv	1,74	0.0
zeta_pv	2,74	0.0
zeta_pv	3,74	0.0
zeta_pv	4,74	0.0
zeta_pv	5,74	0.0
zeta_pv	1,75	0.0
zeta_pv	2,75	0.0
zeta_pv	3,75	0.0
zeta_pv	4,75	0.0
zeta_pv	5,75	0.0
zeta_pv	1,76	0.0
zeta_pv	2,76	0.0
zeta_pv	3,76	0.0
zeta_pv	4,76	0.0
zeta_pv	5,76	0.0
zeta_pv	1,77	0.0
zeta_pv	2,77	0.0
zeta_pv	3,77	0.0
zeta_pv	4,77	0.0
zeta_pv	5,77	0.0
zeta_pv	1,78	0.0
zeta_pv	2,78	0.0
zeta_pv	3,78	0.0
zeta_pv	4,78	0.0
zeta_pv	5,78	0.0
zeta_pv	1,79	0.16467
zeta_pv	2,79	0.16467
zeta_pv	3,79	0.16467
zeta_pv	4,79	0.16467
zeta_pv	5,79	0.16467
zeta_pv	1,80	0.49181
zeta_pv	2,80	0.49181
zeta_pv	3,80	0.49181
zeta_pv	4,80	0.49181
zeta_pv	5,80	0.49181
zeta_pv	1,81	0.87175
zeta_pv	2,81	0.87175
zeta_pv	3,81	0.87175
zeta_pv	4,81	0.87175
zeta_pv	5,81	0.87175
zeta_pv	1,82	0.8922100000000002
zeta_pv	2,82	0.8922100000000002
zeta_pv	3,82	0.8922100000000002
zeta_pv	4,82	0.8922100000000002
zeta_pv	5,82	0.8922100000000002
zeta_pv	1,83	0.8855000000000002
zeta_pv	2,83	0.8855000000000002
zeta_pv	3,83	0.8855000000000002
zeta_pv	4,83	0.8855000000000002
zeta_pv	5,83	0.8855000000000002
zeta_pv	1,84	0.59917
zeta_pv	2,84	0.59917
zeta_pv	3,84	0.59917
zeta_pv	4,84	0.59917
zeta_pv	5,84	0.59917
zeta_pv	1,85	0.72369
zeta_pv	2,85	0.72369
zeta_pv	3,85	0.72369
zeta_pv	4,85	0.72369
zeta_pv	5,85	0.72369
zeta_pv	1,86	0.7103800000000001
zeta_pv	2,86	0.7103800000000001
zeta_pv	3,86	0.7103800000000001
zeta_pv	4,86	0.7103800000000001
zeta_pv	5,86	0.7103800000000001
zeta_pv	1,87	1.1
zeta_pv	2,87	1.1
zeta_pv	3,87	1.1
zeta_pv	4,87	1.1
zeta_pv	5,87	1.1
zeta_pv	1,88	0.91498
zeta_pv	2,88	0.91498
zeta_pv	3,88	0.91498
zeta_pv	4,88	0.91498
zeta_pv	5,88	0.91498
zeta_pv	1,89	1.05952
zeta_pv	2,89	1.05952
zeta_pv	3,89	1.05952
zeta_pv	4,89	1.05952
zeta_pv	5,89	1.05952
zeta_pv	1,90	0.8474400000000001
zeta_pv	2,90	0.8474400000000001
zeta_pv	3,90	0.8474400000000001
zeta_pv	4,90	0.8474400000000001
zeta_pv	5,90	0.8474400000000001
zeta_pv	1,91	0.5574800000000001
zeta_pv	2,91	0.5574800000000001
zeta_pv	3,91	0.5574800000000001
zeta_pv	4,91	0.5574800000000001
zeta_pv	5,91	0.5574800000000001
zeta_pv	1,92	0.36201000000000005
zeta_pv	2,92	0.36201000000000005
zeta_pv	3,92	0.36201000000000005
zeta_pv	4,92	0.36201000000000005
zeta_pv	5,92	0.36201000000000005
zeta_pv	1,93	0.0
zeta_pv	2,93	0.0
zeta_pv	3,93	0.0
zeta_pv	4,93	0.0
zeta_pv	5,93	0.0
zeta_pv	1,94	0.0
zeta_pv	2,94	0.0
zeta_pv	3,94	0.0
zeta_pv	4,94	0.0
zeta_pv	5,94	0.0
zeta_pv	1,95	0.0
zeta_pv	2,95	0.0
zeta_pv	3,95	0.0
zeta_pv	4,95	0.0
zeta_pv	5,95	0.0
zeta_pv	1,96	0.0
zeta_pv	2,96	0.0
zeta_pv	3,96	0.0
zeta_pv	4,96	0.0
zeta_pv	5,96	0.0
zeta_station_pv	1,1	0.0
zeta_station_pv	2,1	0.0
zeta_station_pv	3,1	0.0
zeta_station_pv	4,1	0.0
zeta_station_pv	5,1	0.0
zeta_station_pv	6,1	0.0
zeta_station_pv	7,1	0.0
zeta_station_pv	8,1	0.0
zeta_station_pv	9,1	0.0
zeta_station_pv	10,1	0.0
zeta_station_pv	11,1	0.0
zeta_station_pv	12,1	0.0
zeta_station_pv	13,1	0.0
zeta_station_pv	14,1	0.0
zeta_station_pv	15,1	0.0
zeta_station_pv	16,1	0.0
zeta_station_pv	17,1	0.0
zeta_station_pv	18,1	0.0
zeta_station_pv	19,1	0.0
zeta_station_pv	20,1	0.0
zeta_station_pv	1,2	0.0
zeta_station_pv	2,2	0.0
zeta_station_pv	3,2	0.0
zeta_station_pv	4,2	0.0
zeta_station_pv	5,2	0.0
zeta_station_pv	6,2	0.0
zeta_station_pv	7,2	0.0
zeta_station_pv	8,2	0.0
zeta_station_pv	9,2	0.0
zeta_station_pv	10,2	0.0
zeta_station_pv	11,2	0.0
zeta_station_pv	12,2	0.0
zeta_station_pv	13,2	0.0
zeta_station_pv	14,2	0.0
zeta_station_pv	15,2	0.0
zeta_station_pv	16,2	0.0
zeta_station_pv	17,2	0.0
zeta_station_pv	18,2	0.0
zeta_station_pv	19,2	0.0
zeta_station_pv	20,2	0.0
zeta_station_pv	1,3	0.0
zeta_station_pv	2,3	0.0
zeta_station_pv	3,3	0.0
zeta_station_pv	4,3	0.0
zeta_station_pv	5,3	0.0
zeta_station_pv	6,3	0.0
zeta_station_pv	7,3	0.0
zeta_station_pv	8,3	0.0
zeta_station_pv	9,3	0.0
zeta_station_pv	10,3	0.0
zeta_station_pv	11,3	0.0
zeta_station_pv	12,3	0.0
zeta_station_pv	13,3	0.0
zeta_station_pv	14,3	0.0
zeta_station_pv	15,3	0.0
zeta_station_pv	16,3	0.0
zeta_station_pv	17,3	0.0
zeta_station_pv	18,3	0.0
zeta_station_pv	19,3	0.0
zeta_station_pv	20,3	0.0
zeta_station_pv	1,4	0.0
zeta_station_pv	2,4	0.0
zeta_station_pv	3,4	0.0
zeta_station_pv	4,4	0.0
zeta_station_pv	5,4	0.0
zeta_station_pv	6,4	0.0
zeta_station_pv	7,4	0.0
zeta_station_pv	8,4	0.0
zeta_station_pv	9,4	0.0
zeta_station_pv	10,4	0.0
zeta_station_pv	11,4	0.0
zeta_station_pv	12,4	0.0
zeta_station_pv	13,4	0.0
zeta_station_pv	14,4	0.0
zeta_station_pv	15,4	0.0
zeta_station_pv	16,4	0.0
zeta_station_pv	17,4	0.0
zeta_station_pv	18,4	0.0
zeta_station_pv	19,4	0.0
zeta_station_pv	20,4	0.0
zeta_station_pv	1,5	0.0
zeta_station_pv	2,5	0.0
zeta_station_pv	3,5	0.0
zeta_station_pv	4,5	0.0
zeta_station_pv	5,5	0.0
zeta_station_pv	6,5	0.0
zeta_station_pv	7,5	0.0
zeta_station_pv	8,5	0.0
zeta_station_pv	9,5	0.0
zeta_station_pv	10,5	0.0
zeta_station_pv	11,5	0.0
zeta_station_pv	12,5	0.0
zeta_station_pv	13,5	0.0
zeta_station_pv	14,5	0.0
zeta_station_pv	15,5	0.0
zeta_station_pv	16,5	0.0
zeta_station_pv	17,5	0.0
zeta_station_pv	18,5	0.0
zeta_station_pv	19,5	0.0
zeta_station_pv	20,5	0.0
zeta_station_pv	1,6	0.0
zeta_station_pv	2,6	0.0
zeta_station_pv	3,6	0.0
zeta_station_pv	4,6	0.0
zeta_station_pv	5,6	0.0
zeta_station_pv	6,6	0.0
zeta_station_pv	7,6	0.0
zeta_station_pv	8,6	0.0
zeta_station_pv	9,6	0.0
zeta_station_pv	10,6	0.0
zeta_station_pv	11,6	0.0
zeta_station_pv	12,6	0.0
zeta_station_pv	13,6	0.0
zeta_station_pv	14,6	0.0
zeta_station_pv	15,6	0.0
zeta_station_pv	16,6	0.0
zeta_station_pv	17,6	0.0
zeta_station_pv	18,6	0.0
zeta_station_pv	19,6	0.0
zeta_station_pv	20,6	0.0
zeta_station_pv	1,7	0.16445
zeta_station_pv	2,7	0.16445
zeta_station_pv	3,7	0.16445
zeta_station_pv	4,7	0.16445
zeta_station_pv	5,7	0.16445
zeta_station_pv	6,7	0.16445
zeta_station_pv	7,7	0.16445
zeta_station_pv	8,7	0.16445
zeta_station_pv	9,7	0.16445
zeta_station_pv	10,7	0.16445
zeta_station_pv	11,7	0.16445
zeta_station_pv	12,7	0.16445
zeta_station_pv	13,7	0.16445
zeta_station_pv	14,7	0.16445
zeta_station_pv	15,7	0.16445
zeta_station_pv	16,7	0.16445
zeta_station_pv	17,7	0.16445
zeta_station_pv	18,7	0.16445
zeta_station_pv	19,7	0.16445
zeta_station_pv	20,7	0.16445
zeta_station_pv	1,8	0.49929000000000007
zeta_station_pv	2,8	0.49929000000000007
zeta_station_pv	3,8	0.49929000000000007
zeta_station_pv	4,8	0.49929000000000007
zeta_station_pv	5,8	0.49929000000000007
zeta_station_pv	6,8	0.49929000000000007
zeta_station_pv	7,8	0.49929000000000007
zeta_station_pv	8,8	0.49929000000000007
zeta_station_pv	9,8	0.49929000000000007
zeta_station_pv	10,8	0.49929000000000007
zeta_station_pv	11,8	0.49929000000000007
zeta_station_pv	12,8	0.49929000000000007
zeta_station_pv	13,8	0.49929000000000007
zeta_station_pv	14,8	0.49929000000000007
zeta_station_pv	15,8	0.49929000000000007
zeta_station_pv	16,8	0.49929000000000007
zeta_station_pv	17,8	0.49929000000000007
zeta_station_pv	18,8	0.49929000000000007
zeta_station_pv	19,8	0.49929000000000007
zeta_station_pv	20,8	0.49929000000000007
zeta_station_pv	1,9	0.87736
zeta_station_pv	2,9	0.87736
zeta_station_pv	3,9	0.87736
zeta_station_pv	4,9	0.87736
zeta_station_pv	5,9	0.87736
zeta_station_pv	6,9	0.87736
zeta_station_pv	7,9	0.87736
zeta_station_pv	8,9	0.87736
zeta_station_pv	9,9	0.87736
zeta_station_pv	10,9	0.87736
zeta_station_pv	11,9	0.87736
zeta_station_pv	12,9	0.87736
zeta_station_pv	13,9	0.87736
zeta_station_pv	14,9	0.87736
zeta_station_pv	15,9	0.87736
zeta_station_pv	16,9	0.87736
zeta_station_pv	17,9	0.87736
zeta_station_pv	18,9	0.87736
zeta_station_pv	19,9	0.87736
zeta_station_pv	20,9	0.87736
zeta_station_pv	1,10	0.9201500000000001
zeta_station_pv	2,10	0.9201500000000001
zeta_station_pv	3,10	0.9201500000000001
zeta_station_pv	4,10	0.9201500000000001
zeta_station_pv	5,10	0.9201500000000001
zeta_station_pv	6,10	0.9201500000000001
zeta_station_pv	7,10	0.9201500000000001
zeta_station_pv	8,10	0.9201500000000001
zeta_station_pv	9,10	0.9201500000000001
zeta_station_pv	10,10	0.9201500000000001
zeta_station_pv	11,10	0.9201500000000001
zeta_station_pv	12,10	0.9201500000000001
zeta_station_pv	13,10	0.9201500000000001
zeta_station_pv	14,10	0.9201500000000001
zeta_station_pv	15,10	0.9201500000000001
zeta_station_pv	16,10	0.9201500000000001
zeta_station_pv	17,10	0.9201500000000001
zeta_station_pv	18,10	0.9201500000000001
zeta_station_pv	19,10	0.9201500000000001
zeta_station_pv	20,10	0.9201500000000001
zeta_station_pv	1,11	0.9201500000000001
zeta_station_pv	2,11	0.9201500000000001
zeta_station_pv	3,11	0.9201500000000001
zeta_station_pv	4,11	0.9201500000000001
zeta_station_pv	5,11	0.9201500000000001
zeta_station_pv	6,11	0.9201500000000001
zeta_station_pv	7,11	0.9201500000000001
zeta_station_pv	8,11	0.9201500000000001
zeta_station_pv	9,11	0.9201500000000001
zeta_station_pv	10,11	0.9201500000000001
zeta_station_pv	11,11	0.9201500000000001
zeta_station_pv	12,11	0.9201500000000001
zeta_station_pv	13,11	0.9201500000000001
zeta_station_pv	14,11	0.9201500000000001
zeta_station_pv	15,11	0.9201500000000001
zeta_station_pv	16,11	0.9201500000000001
zeta_station_pv	17,11	0.9201500000000001
zeta_station_pv	18,11	0.9201500000000001
zeta_station_pv	19,11	0.9201500000000001
zeta_station_pv	20,11	0.9201500000000001
zeta_station_pv	1,12	0.6439400000000001
zeta_station_pv	2,12	0.6439400000000001
zeta_station_pv	3,12	0.6439400000000001
zeta_station_pv	4,12	0.6439400000000001
zeta_station_pv	5,12	0.6439400000000001
zeta_station_pv	6,12	0.6439400000000001
zeta_station_pv	7,12	0.6439400000000001
zeta_station_pv	8,12	0.6439400000000001
zeta_station_pv	9,12	0.6439400000000001
zeta_station_pv	10,12	0.6439400000000001
zeta_station_pv	11,12	0.6439400000000001
zeta_station_pv	12,12	0.6439400000000001
zeta_station_pv	13,12	0.6439400000000001
zeta_station_pv	14,12	0.6439400000000001
zeta_station_pv	15,12	0.6439400000000001
zeta_station_pv	16,12	0.6439400000000001
zeta_station_pv	17,12	0.6439400000000001
zeta_station_pv	18,12	0.6439400000000001
zeta_station_pv	19,12	0.6439400000000001
zeta_station_pv	20,12	0.6439400000000001
zeta_station_pv	1,13	0.6952
zeta_station_pv	2,13	0.6952
zeta_station_pv	3,13	0.6952
zeta_station_pv	4,13	0.6952
zeta_station_pv	5,13	0.6952
zeta_station_pv	6,13	0.6952
zeta_station_pv	7,13	0.6952
zeta_station_pv	8,13	0.6952
zeta_station_pv	9,13	0.6952
zeta_station_pv	10,13	0.6952
zeta_station_pv	11,13	0.6952
zeta_station_pv	12,13	0.6952
zeta_station_pv	13,13	0.6952
zeta_station_pv	14,13	0.6952
zeta_station_pv	15,13	0.6952
zeta_station_pv	16,13	0.6952
zeta_station_pv	17,13	0.6952
zeta_station_pv	18,13	0.6952
zeta_station_pv	19,13	0.6952
zeta_station_pv	20,13	0.6952
zeta_station_pv	1,14	0.781
zeta_station_pv	2,14	0.781
zeta_station_pv	3,14	0.781
zeta_station_pv	4,14	0.781
zeta_station_pv	5,14	0.781
zeta_station_pv	6,14	0.781
zeta_station_pv	7,14	0.781
zeta_station_pv	8,14	0.781
zeta_station_pv	9,14	0.781
zeta_station_pv	10,14	0.781
zeta_station_pv	11,14	0.781
zeta_station_pv	12,14	0.781
zeta_station_pv	13,14	0.781
zeta_station_pv	14,14	0.781
zeta_station_pv	15,14	0.781
zeta_station_pv	16,14	0.781
zeta_station_pv	17,14	0.781
zeta_station_pv	18,14	0.781
zeta_station_pv	19,14	0.781
zeta_station_pv	20,14	0.781
zeta_station_pv	1,15	1.04786
zeta_station_pv	2,15	1.04786
zeta_station_pv	3,15	1.04786
zeta_station_pv	4,15	1.04786
zeta_station_pv	5,15	1.04786
zeta_station_pv	6,15	1.04786
zeta_station_pv	7,15	1.04786
zeta_station_pv	8,15	1.04786
zeta_station_pv	9,15	1.04786
zeta_station_pv	10,15	1.04786
zeta_station_pv	11,15	1.04786
zeta_station_pv	12,15	1.04786
zeta_station_pv	13,15	1.04786
zeta_station_pv	14,15	1.04786
zeta_station_pv	15,15	1.04786
zeta_station_pv	16,15	1.04786
zeta_station_pv	17,15	1.04786
zeta_station_pv	18,15	1.04786
zeta_station_pv	19,15	1.04786
zeta_station_pv	20,15	1.04786
zeta_station_pv	1,16	0.8470000000000001
zeta_station_pv	2,16	0.8470000000000001
zeta_station_pv	3,16	0.8470000000000001
zeta_station_pv	4,16	0.8470000000000001
zeta_station_pv	5,16	0.8470000000000001
zeta_station_pv	6,16	0.8470000000000001
zeta_station_pv	7,16	0.8470000000000001
zeta_station_pv	8,16	0.8470000000000001
zeta_station_pv	9,16	0.8470000000000001
zeta_station_pv	10,16	0.8470000000000001
zeta_station_pv	11,16	0.8470000000000001
zeta_station_pv	12,16	0.8470000000000001
zeta_station_pv	13,16	0.8470000000000001
zeta_station_pv	14,16	0.8470000000000001
zeta_station_pv	15,16	0.8470000000000001
zeta_station_pv	16,16	0.8470000000000001
zeta_station_pv	17,16	0.8470000000000001
zeta_station_pv	18,16	0.8470000000000001
zeta_station_pv	19,16	0.8470000000000001
zeta_station_pv	20,16	0.8470000000000001
zeta_station_pv	1,17	0.9542500000000002
zeta_station_pv	2,17	0.9542500000000002
zeta_station_pv	3,17	0.9542500000000002
zeta_station_pv	4,17	0.9542500000000002
zeta_station_pv	5,17	0.9542500000000002
zeta_station_pv	6,17	0.9542500000000002
zeta_station_pv	7,17	0.9542500000000002
zeta_station_pv	8,17	0.9542500000000002
zeta_station_pv	9,17	0.9542500000000002
zeta_station_pv	10,17	0.9542500000000002
zeta_station_pv	11,17	0.9542500000000002
zeta_station_pv	12,17	0.9542500000000002
zeta_station_pv	13,17	0.9542500000000002
zeta_station_pv	14,17	0.9542500000000002
zeta_station_pv	15,17	0.9542500000000002
zeta_station_pv	16,17	0.9542500000000002
zeta_station_pv	17,17	0.9542500000000002
zeta_station_pv	18,17	0.9542500000000002
zeta_station_pv	19,17	0.9542500000000002
zeta_station_pv	20,17	0.9542500000000002
zeta_station_pv	1,18	0.88968
zeta_station_pv	2,18	0.88968
zeta_station_pv	3,18	0.88968
zeta_station_pv	4,18	0.88968
zeta_station_pv	5,18	0.88968
zeta_station_pv	6,18	0.88968
zeta_station_pv	7,18	0.88968
zeta_station_pv	8,18	0.88968
zeta_station_pv	9,18	0.88968
zeta_station_pv	10,18	0.88968
zeta_station_pv	11,18	0.88968
zeta_station_pv	12,18	0.88968
zeta_station_pv	13,18	0.88968
zeta_station_pv	14,18	0.88968
zeta_station_pv	15,18	0.88968
zeta_station_pv	16,18	0.88968
zeta_station_pv	17,18	0.88968
zeta_station_pv	18,18	0.88968
zeta_station_pv	19,18	0.88968
zeta_station_pv	20,18	0.88968
zeta_station_pv	1,19	0.5668300000000001
zeta_station_pv	2,19	0.5668300000000001
zeta_station_pv	3,19	0.5668300000000001
zeta_station_pv	4,19	0.5668300000000001
zeta_station_pv	5,19	0.5668300000000001
zeta_station_pv	6,19	0.5668300000000001
zeta_station_pv	7,19	0.5668300000000001
zeta_station_pv	8,19	0.5668300000000001
zeta_station_pv	9,19	0.5668300000000001
zeta_station_pv	10,19	0.5668300000000001
zeta_station_pv	11,19	0.5668300000000001
zeta_station_pv	12,19	0.5668300000000001
zeta_station_pv	13,19	0.5668300000000001
zeta_station_pv	14,19	0.5668300000000001
zeta_station_pv	15,19	0.5668300000000001
zeta_station_pv	16,19	0.5668300000000001
zeta_station_pv	17,19	0.5668300000000001
zeta_station_pv	18,19	0.5668300000000001
zeta_station_pv	19,19	0.5668300000000001
zeta_station_pv	20,19	0.5668300000000001
zeta_station_pv	1,20	0.38918
zeta_station_pv	2,20	0.38918
zeta_station_pv	3,20	0.38918
zeta_station_pv	4,20	0.38918
zeta_station_pv	5,20	0.38918
zeta_station_pv	6,20	0.38918
zeta_station_pv	7,20	0.38918
zeta_station_pv	8,20	0.38918
zeta_station_pv	9,20	0.38918
zeta_station_pv	10,20	0.38918
zeta_station_pv	11,20	0.38918
zeta_station_pv	12,20	0.38918
zeta_station_pv	13,20	0.38918
zeta_station_pv	14,20	0.38918
zeta_station_pv	15,20	0.38918
zeta_station_pv	16,20	0.38918
zeta_station_pv	17,20	0.38918
zeta_station_pv	18,20	0.38918
zeta_station_pv	19,20	0.38918
zeta_station_pv	20,20	0.38918
zeta_station_pv	1,21	0.0
zeta_station_pv	2,21	0.0
zeta_station_pv	3,21	0.0
zeta_station_pv	4,21	0.0
zeta_station_pv	5,21	0.0
zeta_station_pv	6,21	0.0
zeta_station_pv	7,21	0.0
zeta_station_pv	8,21	0.0
zeta_station_pv	9,21	0.0
zeta_station_pv	10,21	0.0
zeta_station_pv	11,21	0.0
zeta_station_pv	12,21	0.0
zeta_station_pv	13,21	0.0
zeta_station_pv	14,21	0.0
zeta_station_pv	15,21	0.0
zeta_station_pv	16,21	0.0
zeta_station_pv	17,21	0.0
zeta_station_pv	18,21	0.0
zeta_station_pv	19,21	0.0
zeta_station_pv	20,21	0.0
zeta_station_pv	1,22	0.0
zeta_station_pv	2,22	0.0
zeta_station_pv	3,22	0.0
zeta_station_pv	4,22	0.0
zeta_station_pv	5,22	0.0
zeta_station_pv	6,22	0.0
zeta_station_pv	7,22	0.0
zeta_station_pv	8,22	0.0
zeta_station_pv	9,22	0.0
zeta_station_pv	10,22	0.0
zeta_station_pv	11,22	0.0
zeta_station_pv	12,22	0.0
zeta_station_pv	13,22	0.0
zeta_station_pv	14,22	0.0
zeta_station_pv	15,22	0.0
zeta_station_pv	16,22	0.0
zeta_station_pv	17,22	0.0
zeta_station_pv	18,22	0.0
zeta_station_pv	19,22	0.0
zeta_station_pv	20,22	0.0
zeta_station_pv	1,23	0.0
zeta_station_pv	2,23	0.0
zeta_station_pv	3,23	0.0
zeta_station_pv	4,23	0.0
zeta_station_pv	5,23	0.0
zeta_station_pv	6,23	0.0
zeta_station_pv	7,23	0.0
zeta_station_pv	8,23	0.0
zeta_station_pv	9,23	0.0
zeta_station_pv	10,23	0.0
zeta_station_pv	11,23	0.0
zeta_station_pv	12,23	0.0
zeta_station_pv	13,23	0.0
zeta_station_pv	14,23	0.0
zeta_station_pv	15,23	0.0
zeta_station_pv	16,23	0.0
zeta_station_pv	17,23	0.0
zeta_station_pv	18,23	0.0
zeta_station_pv	19,23	0.0
zeta_station_pv	20,23	0.0
zeta_station_pv	1,24	0.0
zeta_station_pv	2,24	0.0
zeta_station_pv	3,24	0.0
zeta_station_pv	4,24	0.0
zeta_station_pv	5,24	0.0
zeta_station_pv	6,24	0.0
zeta_station_pv	7,24	0.0
zeta_station_pv	8,24	0.0
zeta_station_pv	9,24	0.0
zeta_station_pv	10,24	0.0
zeta_station_pv	11,24	0.0
zeta_station_pv	12,24	0.0
zeta_station_pv	13,24	0.0
zeta_station_pv	14,24	0.0
zeta_station_pv	15,24	0.0
zeta_station_pv	16,24	0.0
zeta_station_pv	17,24	0.0
zeta_station_pv	18,24	0.0
zeta_station_pv	19,24	0.0
zeta_station_pv	20,24	0.0
zeta_station_pv	1,25	0.0
zeta_station_pv	2,25	0.0
zeta_station_pv	3,25	0.0
zeta_station_pv	4,25	0.0
zeta_station_pv	5,25	0.0
zeta_station_pv	6,25	0.0
zeta_station_pv	7,25	0.0
zeta_station_pv	8,25	0.0
zeta_station_pv	9,25	0.0
zeta_station_pv	10,25	0.0
zeta_station_pv	11,25	0.0
zeta_station_pv	12,25	0.0
zeta_station_pv	13,25	0.0
zeta_station_pv	14,25	0.0
zeta_station_pv	15,25	0.0
zeta_station_pv	16,25	0.0
zeta_station_pv	17,25	0.0
zeta_station_pv	18,25	0.0
zeta_station_pv	19,25	0.0
zeta_station_pv	20,25	0.0
zeta_station_pv	1,26	0.0
zeta_station_pv	2,26	0.0
zeta_station_pv	3,26	0.0
zeta_station_pv	4,26	0.0
zeta_station_pv	5,26	0.0
zeta_station_pv	6,26	0.0
zeta_station_pv	7,26	0.0
zeta_station_pv	8,26	0.0
zeta_station_pv	9,26	0.0
zeta_station_pv	10,26	0.0
zeta_station_pv	11,26	0.0
zeta_station_pv	12,26	0.0
zeta_station_pv	13,26	0.0
zeta_station_pv	14,26	0.0
zeta_station_pv	15,26	0.0
zeta_station_pv	16,26	0.0
zeta_station_pv	17,26	0.0
zeta_station_pv	18,26	0.0
zeta_station_pv	19,26	0.0
zeta_station_pv	20,26	0.0
zeta_station_pv	1,27	0.0
zeta_station_pv	2,27	0.0
zeta_station_pv	3,27	0.0
zeta_station_pv	4,27	0.0
zeta_station_pv	5,27	0.0
zeta_station_pv	6,27	0.0
zeta_station_pv	7,27	0.0
zeta_station_pv	8,27	0.0
zeta_station_pv	9,27	0.0
zeta_station_pv	10,27	0.0
zeta_station_pv	11,27	0.0
zeta_station_pv	12,27	0.0
zeta_station_pv	13,27	0.0
zeta_station_pv	14,27	0.0
zeta_station_pv	15,27	0.0
zeta_station_pv	16,27	0.0
zeta_station_pv	17,27	0.0
zeta_station_pv	18,27	0.0
zeta_station_pv	19,27	0.0
zeta_station_pv	20,27	0.0
zeta_station_pv	1,28	0.0
zeta_station_pv	2,28	0.0
zeta_station_pv	3,28	0.0
zeta_station_pv	4,28	0.0
zeta_station_pv	5,28	0.0
zeta_station_pv	6,28	0.0
zeta_station_pv	7,28	0.0
zeta_station_pv	8,28	0.0
zeta_station_pv	9,28	0.0
zeta_station_pv	10,28	0.0
zeta_station_pv	11,28	0.0
zeta_station_pv	12,28	0.0
zeta_station_pv	13,28	0.0
zeta_station_pv	14,28	0.0
zeta_station_pv	15,28	0.0
zeta_station_pv	16,28	0.0
zeta_station_pv	17,28	0.0
zeta_station_pv	18,28	0.0
zeta_station_pv	19,28	0.0
zeta_station_pv	20,28	0.0
zeta_station_pv	1,29	0.0
zeta_station_pv	2,29	0.0
zeta_station_pv	3,29	0.0
zeta_station_pv	4,29	0.0
zeta_station_pv	5,29	0.0
zeta_station_pv	6,29	0.0
zeta_station_pv	7,29	0.0
zeta_station_pv	8,29	0.0
zeta_station_pv	9,29	0.0
zeta_station_pv	10,29	0.0
zeta_station_pv	11,29	0.0
zeta_station_pv	12,29	0.0
zeta_station_pv	13,29	0.0
zeta_station_pv	14,29	0.0
zeta_station_pv	15,29	0.0
zeta_station_pv	16,29	0.0
zeta_station_pv	17,29	0.0
zeta_station_pv	18,29	0.0
zeta_station_pv	19,29	0.0
zeta_station_pv	20,29	0.0
zeta_station_pv	1,30	0.0
zeta_station_pv	2,30	0.0
zeta_station_pv	3,30	0.0
zeta_station_pv	4,30	0.0
zeta_station_pv	5,30	0.0
zeta_station_pv	6,30	0.0
zeta_station_pv	7,30	0.0
zeta_station_pv	8,30	0.0
zeta_station_pv	9,30	0.0
zeta_station_pv	10,30	0.0
zeta_station_pv	11,30	0.0
zeta_station_pv	12,30	0.0
zeta_station_pv	13,30	0.0
zeta_station_pv	14,30	0.0
zeta_station_pv	15,30	0.0
zeta_station_pv	16,30	0.0
zeta_station_pv	17,30	0.0
zeta_station_pv	18,30	0.0
zeta_station_pv	19,30	0.0
zeta_station_pv	20,30	0.0
zeta_station_pv	1,31	0.14399
zeta_station_pv	2,31	0.14399
zeta_station_pv	3,31	0.14399
zeta_station_pv	4,31	0.14399
zeta_station_pv	5,31	0.14399
zeta_station_pv	6,31	0.14399
zeta_station_pv	7,31	0.14399
zeta_station_pv	8,31	0.14399
zeta_station_pv	9,31	0.14399
zeta_station_pv	10,31	0.14399
zeta_station_pv	11,31	0.14399
zeta_station_pv	12,31	0.14399
zeta_station_pv	13,31	0.14399
zeta_station_pv	14,31	0.14399
zeta_station_pv	15,31	0.14399
zeta_station_pv	16,31	0.14399
zeta_station_pv	17,31	0.14399
zeta_station_pv	18,31	0.14399
zeta_station_pv	19,31	0.14399
zeta_station_pv	20,31	0.14399
zeta_station_pv	1,32	0.53119
zeta_station_pv	2,32	0.53119
zeta_station_pv	3,32	0.53119
zeta_station_pv	4,32	0.53119
zeta_station_pv	5,32	0.53119
zeta_station_pv	6,32	0.53119
zeta_station_pv	7,32	0.53119
zeta_station_pv	8,32	0.53119
zeta_station_pv	9,32	0.53119
zeta_station_pv	10,32	0.53119
zeta_station_pv	11,32	0.53119
zeta_station_pv	12,32	0.53119
zeta_station_pv	13,32	0.53119
zeta_station_pv	14,32	0.53119
zeta_station_pv	15,32	0.53119
zeta_station_pv	16,32	0.53119
zeta_station_pv	17,32	0.53119
zeta_station_pv	18,32	0.53119
zeta_station_pv	19,32	0.53119
zeta_station_pv	20,32	0.53119
zeta_station_pv	1,33	0.8193900000000001
zeta_station_pv	2,33	0.8193900000000001
zeta_station_pv	3,33	0.8193900000000001
zeta_station_pv	4,33	0.8193900000000001
zeta_station_pv	5,33	0.8193900000000001
zeta_station_pv	6,33	0.8193900000000001
zeta_station_pv	7,33	0.8193900000000001
zeta_station_pv	8,33	0.8193900000000001
zeta_station_pv	9,33	0.8193900000000001
zeta_station_pv	10,33	0.8193900000000001
zeta_station_pv	11,33	0.8193900000000001
zeta_station_pv	12,33	0.8193900000000001
zeta_station_pv	13,33	0.8193900000000001
zeta_station_pv	14,33	0.8193900000000001
zeta_station_pv	15,33	0.8193900000000001
zeta_station_pv	16,33	0.8193900000000001
zeta_station_pv	17,33	0.8193900000000001
zeta_station_pv	18,33	0.8193900000000001
zeta_station_pv	19,33	0.8193900000000001
zeta_station_pv	20,33	0.8193900000000001
zeta_station_pv	1,34	0.81763
zeta_station_pv	2,34	0.81763
zeta_station_pv	3,34	0.81763
zeta_station_pv	4,34	0.81763
zeta_station_pv	5,34	0.81763
zeta_station_pv	6,34	0.81763
zeta_station_pv	7,34	0.81763
zeta_station_pv	8,34	0.81763
zeta_station_pv	9,34	0.81763
zeta_station_pv	10,34	0.81763
zeta_station_pv	11,34	0.81763
zeta_station_pv	12,34	0.81763
zeta_station_pv	13,34	0.81763
zeta_station_pv	14,34	0.81763
zeta_station_pv	15,34	0.81763
zeta_station_pv	16,34	0.81763
zeta_station_pv	17,34	0.81763
zeta_station_pv	18,34	0.81763
zeta_station_pv	19,34	0.81763
zeta_station_pv	20,34	0.81763
zeta_station_pv	1,35	1.0418100000000001
zeta_station_pv	2,35	1.0418100000000001
zeta_station_pv	3,35	1.0418100000000001
zeta_station_pv	4,35	1.0418100000000001
zeta_station_pv	5,35	1.0418100000000001
zeta_station_pv	6,35	1.0418100000000001
zeta_station_pv	7,35	1.0418100000000001
zeta_station_pv	8,35	1.0418100000000001
zeta_station_pv	9,35	1.0418100000000001
zeta_station_pv	10,35	1.0418100000000001
zeta_station_pv	11,35	1.0418100000000001
zeta_station_pv	12,35	1.0418100000000001
zeta_station_pv	13,35	1.0418100000000001
zeta_station_pv	14,35	1.0418100000000001
zeta_station_pv	15,35	1.0418100000000001
zeta_station_pv	16,35	1.0418100000000001
zeta_station_pv	17,35	1.0418100000000001
zeta_station_pv	18,35	1.0418100000000001
zeta_station_pv	19,35	1.0418100000000001
zeta_station_pv	20,35	1.0418100000000001
zeta_station_pv	1,36	0.66352
zeta_station_pv	2,36	0.66352
zeta_station_pv	3,36	0.66352
zeta_station_pv	4,36	0.66352
zeta_station_pv	5,36	0.66352
zeta_station_pv	6,36	0.66352
zeta_station_pv	7,36	0.66352
zeta_station_pv	8,36	0.66352
zeta_station_pv	9,36	0.66352
zeta_station_pv	10,36	0.66352
zeta_station_pv	11,36	0.66352
zeta_station_pv	12,36	0.66352
zeta_station_pv	13,36	0.66352
zeta_station_pv	14,36	0.66352
zeta_station_pv	15,36	0.66352
zeta_station_pv	16,36	0.66352
zeta_station_pv	17,36	0.66352
zeta_station_pv	18,36	0.66352
zeta_station_pv	19,36	0.66352
zeta_station_pv	20,36	0.66352
zeta_station_pv	1,37	0.67903
zeta_station_pv	2,37	0.67903
zeta_station_pv	3,37	0.67903
zeta_station_pv	4,37	0.67903
zeta_station_pv	5,37	0.67903
zeta_station_pv	6,37	0.67903
zeta_station_pv	7,37	0.67903
zeta_station_pv	8,37	0.67903
zeta_station_pv	9,37	0.67903
zeta_station_pv	10,37	0.67903
zeta_station_pv	11,37	0.67903
zeta_station_pv	12,37	0.67903
zeta_station_pv	13,37	0.67903
zeta_station_pv	14,37	0.67903
zeta_station_pv	15,37	0.67903
zeta_station_pv	16,37	0.67903
zeta_station_pv	17,37	0.67903
zeta_station_pv	18,37	0.67903
zeta_station_pv	19,37	0.67903
zeta_station_pv	20,37	0.67903
zeta_station_pv	1,38	0.75438
zeta_station_pv	2,38	0.75438
zeta_station_pv	3,38	0.75438
zeta_station_pv	4,38	0.75438
zeta_station_pv	5,38	0.75438
zeta_station_pv	6,38	0.75438
zeta_station_pv	7,38	0.75438
zeta_station_pv	8,38	0.75438
zeta_station_pv	9,38	0.75438
zeta_station_pv	10,38	0.75438
zeta_station_pv	11,38	0.75438
zeta_station_pv	12,38	0.75438
zeta_station_pv	13,38	0.75438
zeta_station_pv	14,38	0.75438
zeta_station_pv	15,38	0.75438
zeta_station_pv	16,38	0.75438
zeta_station_pv	17,38	0.75438
zeta_station_pv	18,38	0.75438
zeta_station_pv	19,38	0.75438
zeta_station_pv	20,38	0.75438
zeta_station_pv	1,39	1.00254
zeta_station_pv	2,39	1.00254
zeta_station_pv	3,39	1.00254
zeta_station_pv	4,39	1.00254
zeta_station_pv	5,39	1.00254
zeta_station_pv	6,39	1.00254
zeta_station_pv	7,39	1.00254
zeta_station_pv	8,39	1.00254
zeta_station_pv	9,39	1.00254
zeta_station_pv	10,39	1.00254
zeta_station_pv	11,39	1.00254
zeta_station_pv	12,39	1.00254
zeta_station_pv	13,39	1.00254
zeta_station_pv	14,39	1.00254
zeta_station_pv	15,39	1.00254
zeta_station_pv	16,39	1.00254
zeta_station_pv	17,39	1.00254
zeta_station_pv	18,39	1.00254
zeta_station_pv	19,39	1.00254
zeta_station_pv	20,39	1.00254
zeta_station_pv	1,40	0.9321400000000001
zeta_station_pv	2,40	0.9321400000000001
zeta_station_pv	3,40	0.9321400000000001
zeta_station_pv	4,40	0.9321400000000001
zeta_station_pv	5,40	0.9321400000000001
zeta_station_pv	6,40	0.9321400000000001
zeta_station_pv	7,40	0.9321400000000001
zeta_station_pv	8,40	0.9321400000000001
zeta_station_pv	9,40	0.9321400000000001
zeta_station_pv	10,40	0.9321400000000001
zeta_station_pv	11,40	0.9321400000000001
zeta_station_pv	12,40	0.9321400000000001
zeta_station_pv	13,40	0.9321400000000001
zeta_station_pv	14,40	0.9321400000000001
zeta_station_pv	15,40	0.9321400000000001
zeta_station_pv	16,40	0.9321400000000001
zeta_station_pv	17,40	0.9321400000000001
zeta_station_pv	18,40	0.9321400000000001
zeta_station_pv	19,40	0.9321400000000001
zeta_station_pv	20,40	0.9321400000000001
zeta_station_pv	1,41	0.9462200000000001
zeta_station_pv	2,41	0.9462200000000001
zeta_station_pv	3,41	0.9462200000000001
zeta_station_pv	4,41	0.9462200000000001
zeta_station_pv	5,41	0.9462200000000001
zeta_station_pv	6,41	0.9462200000000001
zeta_station_pv	7,41	0.9462200000000001
zeta_station_pv	8,41	0.9462200000000001
zeta_station_pv	9,41	0.9462200000000001
zeta_station_pv	10,41	0.9462200000000001
zeta_station_pv	11,41	0.9462200000000001
zeta_station_pv	12,41	0.9462200000000001
zeta_station_pv	13,41	0.9462200000000001
zeta_station_pv	14,41	0.9462200000000001
zeta_station_pv	15,41	0.9462200000000001
zeta_station_pv	16,41	0.9462200000000001
zeta_station_pv	17,41	0.9462200000000001
zeta_station_pv	18,41	0.9462200000000001
zeta_station_pv	19,41	0.9462200000000001
zeta_station_pv	20,41	0.9462200000000001
zeta_station_pv	1,42	0.8115800000000001
zeta_station_pv	2,42	0.8115800000000001
zeta_station_pv	3,42	0.8115800000000001
zeta_station_pv	4,42	0.8115800000000001
zeta_station_pv	5,42	0.8115800000000001
zeta_station_pv	6,42	0.8115800000000001
zeta_station_pv	7,42	0.8115800000000001
zeta_station_pv	8,42	0.8115800000000001
zeta_station_pv	9,42	0.8115800000000001
zeta_station_pv	10,42	0.8115800000000001
zeta_station_pv	11,42	0.8115800000000001
zeta_station_pv	12,42	0.8115800000000001
zeta_station_pv	13,42	0.8115800000000001
zeta_station_pv	14,42	0.8115800000000001
zeta_station_pv	15,42	0.8115800000000001
zeta_station_pv	16,42	0.8115800000000001
zeta_station_pv	17,42	0.8115800000000001
zeta_station_pv	18,42	0.8115800000000001
zeta_station_pv	19,42	0.8115800000000001
zeta_station_pv	20,42	0.8115800000000001
zeta_station_pv	1,43	0.6298600000000001
zeta_station_pv	2,43	0.6298600000000001
zeta_station_pv	3,43	0.6298600000000001
zeta_station_pv	4,43	0.6298600000000001
zeta_station_pv	5,43	0.6298600000000001
zeta_station_pv	6,43	0.6298600000000001
zeta_station_pv	7,43	0.6298600000000001
zeta_station_pv	8,43	0.6298600000000001
zeta_station_pv	9,43	0.6298600000000001
zeta_station_pv	10,43	0.6298600000000001
zeta_station_pv	11,43	0.6298600000000001
zeta_station_pv	12,43	0.6298600000000001
zeta_station_pv	13,43	0.6298600000000001
zeta_station_pv	14,43	0.6298600000000001
zeta_station_pv	15,43	0.6298600000000001
zeta_station_pv	16,43	0.6298600000000001
zeta_station_pv	17,43	0.6298600000000001
zeta_station_pv	18,43	0.6298600000000001
zeta_station_pv	19,43	0.6298600000000001
zeta_station_pv	20,43	0.6298600000000001
zeta_station_pv	1,44	0.39193000000000006
zeta_station_pv	2,44	0.39193000000000006
zeta_station_pv	3,44	0.39193000000000006
zeta_station_pv	4,44	0.39193000000000006
zeta_station_pv	5,44	0.39193000000000006
zeta_station_pv	6,44	0.39193000000000006
zeta_station_pv	7,44	0.39193000000000006
zeta_station_pv	8,44	0.39193000000000006
zeta_station_pv	9,44	0.39193000000000006
zeta_station_pv	10,44	0.39193000000000006
zeta_station_pv	11,44	0.39193000000000006
zeta_station_pv	12,44	0.39193000000000006
zeta_station_pv	13,44	0.39193000000000006
zeta_station_pv	14,44	0.39193000000000006
zeta_station_pv	15,44	0.39193000000000006
zeta_station_pv	16,44	0.39193000000000006
zeta_station_pv	17,44	0.39193000000000006
zeta_station_pv	18,44	0.39193000000000006
zeta_station_pv	19,44	0.39193000000000006
zeta_station_pv	20,44	0.39193000000000006
zeta_station_pv	1,45	0.0
zeta_station_pv	2,45	0.0
zeta_station_pv	3,45	0.0
zeta_station_pv	4,45	0.0
zeta_station_pv	5,45	0.0
zeta_station_pv	6,45	0.0
zeta_station_pv	7,45	0.0
zeta_station_pv	8,45	0.0
zeta_station_pv	9,45	0.0
zeta_station_pv	10,45	0.0
zeta_station_pv	11,45	0.0
zeta_station_pv	12,45	0.0
zeta_station_pv	13,45	0.0
zeta_station_pv	14,45	0.0
zeta_station_pv	15,45	0.0
zeta_station_pv	16,45	0.0
zeta_station_pv	17,45	0.0
zeta_station_pv	18,45	0.0
zeta_station_pv	19,45	0.0
zeta_station_pv	20,45	0.0
zeta_station_pv	1,46	0.0
zeta_station_pv	2,46	0.0
zeta_station_pv	3,46	0.0
zeta_station_pv	4,46	0.0
zeta_station_pv	5,46	0.0
zeta_station_pv	6,46	0.0
zeta_station_pv	7,46	0.0
zeta_station_pv	8,46	0.0
zeta_station_pv	9,46	0.0
zeta_station_pv	10,46	0.0
zeta_station_pv	11,46	0.0
zeta_station_pv	12,46	0.0
zeta_station_pv	13,46	0.0
zeta_station_pv	14,46	0.0
zeta_station_pv	15,46	0.0
zeta_station_pv	16,46	0.0
zeta_station_pv	17,46	0.0
zeta_station_pv	18,46	0.0
zeta_station_pv	19,46	0.0
zeta_station_pv	20,46	0.0
zeta_station_pv	1,47	0.0
zeta_station_pv	2,47	0.0
zeta_station_pv	3,47	0.0
zeta_station_pv	4,47	0.0
zeta_station_pv	5,47	0.0
zeta_station_pv	6,47	0.0
zeta_station_pv	7,47	0.0
zeta_station_pv	8,47	0.0
zeta_station_pv	9,47	0.0
zeta_station_pv	10,47	0.0
zeta_station_pv	11,47	0.0
zeta_station_pv	12,47	0.0
zeta_station_pv	13,47	0.0
zeta_station_pv	14,47	0.0
zeta_station_pv	15,47	0.0
zeta_station_pv	16,47	0.0
zeta_station_pv	17,47	0.0
zeta_station_pv	18,47	0.0
zeta_station_pv	19,47	0.0
zeta_station_pv	20,47	0.0
zeta_station_pv	1,48	0.0
zeta_station_pv	2,48	0.0
zeta_station_pv	3,48	0.0
zeta_station_pv	4,48	0.0
zeta_station_pv	5,48	0.0
zeta_station_pv	6,48	0.0
zeta_station_pv	7,48	0.0
zeta_station_pv	8,48	0.0
zeta_station_pv	9,48	0.0
zeta_station_pv	10,48	0.0
zeta_station_pv	11,48	0.0
zeta_station_pv	12,48	0.0
zeta_station_pv	13,48	0.0
zeta_station_pv	14,48	0.0
zeta_station_pv	15,48	0.0
zeta_station_pv	16,48	0.0
zeta_station_pv	17,48	0.0
zeta_station_pv	18,48	0.0
zeta_station_pv	19,48	0.0
zeta_station_pv	20,48	0.0
zeta_station_pv	1,49	0.0
zeta_station_pv	2,49	0.0
zeta_station_pv	3,49	0.0
zeta_station_pv	4,49	0.0
zeta_station_pv	5,49	0.0
zeta_station_pv	6,49	0.0
zeta_station_pv	7,49	0.0
zeta_station_pv	8,49	0.0
zeta_station_pv	9,49	0.0
zeta_station_pv	10,49	0.0
zeta_station_pv	11,49	0.0
zeta_station_pv	12,49	0.0
zeta_station_pv	13,49	0.0
zeta_station_pv	14,49	0.0
zeta_station_pv	15,49	0.0
zeta_station_pv	16,49	0.0
zeta_station_pv	17,49	0.0
zeta_station_pv	18,49	0.0
zeta_station_pv	19,49	0.0
zeta_station_pv	20,49	0.0
zeta_station_pv	1,50	0.0
zeta_station_pv	2,50	0.0
zeta_station_pv	3,50	0.0
zeta_station_pv	4,50	0.0
zeta_station_pv	5,50	0.0
zeta_station_pv	6,50	0.0
zeta_station_pv	7,50	0.0
zeta_station_pv	8,50	0.0
zeta_station_pv	9,50	0.0
zeta_station_pv	10,50	0.0
zeta_station_pv	11,50	0.0
zeta_station_pv	12,50	0.0
zeta_station_pv	13,50	0.0
zeta_station_pv	14,50	0.0
zeta_station_pv	15,50	0.0
zeta_station_pv	16,50	0.0
zeta_station_pv	17,50	0.0
zeta_station_pv	18,50	0.0
zeta_station_pv	19,50	0.0
zeta_station_pv	20,50	0.0
zeta_station_pv	1,51	0.0
zeta_station_pv	2,51	0.0
zeta_station_pv	3,51	0.0
zeta_station_pv	4,51	0.0
zeta_station_pv	5,51	0.0
zeta_station_pv	6,51	0.0
zeta_station_pv	7,51	0.0
zeta_station_pv	8,51	0.0
zeta_station_pv	9,51	0.0
zeta_station_pv	10,51	0.0
zeta_station_pv	11,51	0.0
zeta_station_pv	12,51	0.0
zeta_station_pv	13,51	0.0
zeta_station_pv	14,51	0.0
zeta_station_pv	15,51	0.0
zeta_station_pv	16,51	0.0
zeta_station_pv	17,51	0.0
zeta_station_pv	18,51	0.0
zeta_station_pv	19,51	0.0
zeta_station_pv	20,51	0.0
zeta_station_pv	1,52	0.0
zeta_station_pv	2,52	0.0
zeta_station_pv	3,52	0.0
zeta_station_pv	4,52	0.0
zeta_station_pv	5,52	0.0
zeta_station_pv	6,52	0.0
zeta_station_pv	7,52	0.0
zeta_station_pv	8,52	0.0
zeta_station_pv	9,52	0.0
zeta_station_pv	10,52	0.0
zeta_station_pv	11,52	0.0
zeta_station_pv	12,52	0.0
zeta_station_pv	13,52	0.0
zeta_station_pv	14,52	0.0
zeta_station_pv	15,52	0.0
zeta_station_pv	16,52	0.0
zeta_station_pv	17,52	0.0
zeta_station_pv	18,52	0.0
zeta_station_pv	19,52	0.0
zeta_station_pv	20,52	0.0
zeta_station_pv	1,53	0.0
zeta_station_pv	2,53	0.0
zeta_station_pv	3,53	0.0
zeta_station_pv	4,53	0.0
zeta_station_pv	5,53	0.0
zeta_station_pv	6,53	0.0
zeta_station_pv	7,53	0.0
zeta_station_pv	8,53	0.0
zeta_station_pv	9,53	0.0
zeta_station_pv	10,53	0.0
zeta_station_pv	11,53	0.0
zeta_station_pv	12,53	0.0
zeta_station_pv	13,53	0.0
zeta_station_pv	14,53	0.0
zeta_station_pv	15,53	0.0
zeta_station_pv	16,53	0.0
zeta_station_pv	17,53	0.0
zeta_station_pv	18,53	0.0
zeta_station_pv	19,53	0.0
zeta_station_pv	20,53	0.0
zeta_station_pv	1,54	0.0
zeta_station_pv	2,54	0.0
zeta_station_pv	3,54	0.0
zeta_station_pv	4,54	0.0
zeta_station_pv	5,54	0.0
zeta_station_pv	6,54	0.0
zeta_station_pv	7,54	0.0
zeta_station_pv	8,54	0.0
zeta_station_pv	9,54	0.0
zeta_station_pv	10,54	0.0
zeta_station_pv	11,54	0.0
zeta_station_pv	12,54	0.0
zeta_station_pv	13,54	0.0
zeta_station_pv	14,54	0.0
zeta_station_pv	15,54	0.0
zeta_station_pv	16,54	0.0
zeta_station_pv	17,54	0.0
zeta_station_pv	18,54	0.0
zeta_station_pv	19,54	0.0
zeta_station_pv	20,54	0.0
zeta_station_pv	1,55	0.16995000000000002
zeta_station_pv	2,55	0.16995000000000002
zeta_station_pv	3,55	0.16995000000000002
zeta_station_pv	4,55	0.16995000000000002
zeta_station_pv	5,55	0.16995000000000002
zeta_station_pv	6,55	0.16995000000000002
zeta_station_pv	7,55	0.16995000000000002
zeta_station_pv	8,55	0.16995000000000002
zeta_station_pv	9,55	0.16995000000000002
zeta_station_pv	10,55	0.16995000000000002
zeta_station_pv	11,55	0.16995000000000002
zeta_station_pv	12,55	0.16995000000000002
zeta_station_pv	13,55	0.16995000000000002
zeta_station_pv	14,55	0.16995000000000002
zeta_station_pv	15,55	0.16995000000000002
zeta_station_pv	16,55	0.16995000000000002
zeta_station_pv	17,55	0.16995000000000002
zeta_station_pv	18,55	0.16995000000000002
zeta_station_pv	19,55	0.16995000000000002
zeta_station_pv	20,55	0.16995000000000002
zeta_station_pv	1,56	0.5397700000000001
zeta_station_pv	2,56	0.5397700000000001
zeta_station_pv	3,56	0.5397700000000001
zeta_station_pv	4,56	0.5397700000000001
zeta_station_pv	5,56	0.5397700000000001
zeta_station_pv	6,56	0.5397700000000001
zeta_station_pv	7,56	0.5397700000000001
zeta_station_pv	8,56	0.5397700000000001
zeta_station_pv	9,56	0.5397700000000001
zeta_station_pv	10,56	0.5397700000000001
zeta_station_pv	11,56	0.5397700000000001
zeta_station_pv	12,56	0.5397700000000001
zeta_station_pv	13,56	0.5397700000000001
zeta_station_pv	14,56	0.5397700000000001
zeta_station_pv	15,56	0.5397700000000001
zeta_station_pv	16,56	0.5397700000000001
zeta_station_pv	17,56	0.5397700000000001
zeta_station_pv	18,56	0.5397700000000001
zeta_station_pv	19,56	0.5397700000000001
zeta_station_pv	20,56	0.5397700000000001
zeta_station_pv	1,57	0.79508
zeta_station_pv	2,57	0.79508
zeta_station_pv	3,57	0.79508
zeta_station_pv	4,57	0.79508
zeta_station_pv	5,57	0.79508
zeta_station_pv	6,57	0.79508
zeta_station_pv	7,57	0.79508
zeta_station_pv	8,57	0.79508
zeta_station_pv	9,57	0.79508
zeta_station_pv	10,57	0.79508
zeta_station_pv	11,57	0.79508
zeta_station_pv	12,57	0.79508
zeta_station_pv	13,57	0.79508
zeta_station_pv	14,57	0.79508
zeta_station_pv	15,57	0.79508
zeta_station_pv	16,57	0.79508
zeta_station_pv	17,57	0.79508
zeta_station_pv	18,57	0.79508
zeta_station_pv	19,57	0.79508
zeta_station_pv	20,57	0.79508
zeta_station_pv	1,58	0.9424800000000001
zeta_station_pv	2,58	0.9424800000000001
zeta_station_pv	3,58	0.9424800000000001
zeta_station_pv	4,58	0.9424800000000001
zeta_station_pv	5,58	0.9424800000000001
zeta_station_pv	6,58	0.9424800000000001
zeta_station_pv	7,58	0.9424800000000001
zeta_station_pv	8,58	0.9424800000000001
zeta_station_pv	9,58	0.9424800000000001
zeta_station_pv	10,58	0.9424800000000001
zeta_station_pv	11,58	0.9424800000000001
zeta_station_pv	12,58	0.9424800000000001
zeta_station_pv	13,58	0.9424800000000001
zeta_station_pv	14,58	0.9424800000000001
zeta_station_pv	15,58	0.9424800000000001
zeta_station_pv	16,58	0.9424800000000001
zeta_station_pv	17,58	0.9424800000000001
zeta_station_pv	18,58	0.9424800000000001
zeta_station_pv	19,58	0.9424800000000001
zeta_station_pv	20,58	0.9424800000000001
zeta_station_pv	1,59	0.9953900000000001
zeta_station_pv	2,59	0.9953900000000001
zeta_station_pv	3,59	0.9953900000000001
zeta_station_pv	4,59	0.9953900000000001
zeta_station_pv	5,59	0.9953900000000001
zeta_station_pv	6,59	0.9953900000000001
zeta_station_pv	7,59	0.9953900000000001
zeta_station_pv	8,59	0.9953900000000001
zeta_station_pv	9,59	0.9953900000000001
zeta_station_pv	10,59	0.9953900000000001
zeta_station_pv	11,59	0.9953900000000001
zeta_station_pv	12,59	0.9953900000000001
zeta_station_pv	13,59	0.9953900000000001
zeta_station_pv	14,59	0.9953900000000001
zeta_station_pv	15,59	0.9953900000000001
zeta_station_pv	16,59	0.9953900000000001
zeta_station_pv	17,59	0.9953900000000001
zeta_station_pv	18,59	0.9953900000000001
zeta_station_pv	19,59	0.9953900000000001
zeta_station_pv	20,59	0.9953900000000001
zeta_station_pv	1,60	0.63811
zeta_station_pv	2,60	0.63811
zeta_station_pv	3,60	0.63811
zeta_station_pv	4,60	0.63811
zeta_station_pv	5,60	0.63811
zeta_station_pv	6,60	0.63811
zeta_station_pv	7,60	0.63811
zeta_station_pv	8,60	0.63811
zeta_station_pv	9,60	0.63811
zeta_station_pv	10,60	0.63811
zeta_station_pv	11,60	0.63811
zeta_station_pv	12,60	0.63811
zeta_station_pv	13,60	0.63811
zeta_station_pv	14,60	0.63811
zeta_station_pv	15,60	0.63811
zeta_station_pv	16,60	0.63811
zeta_station_pv	17,60	0.63811
zeta_station_pv	18,60	0.63811
zeta_station_pv	19,60	0.63811
zeta_station_pv	20,60	0.63811
zeta_station_pv	1,61	0.6620900000000001
zeta_station_pv	2,61	0.6620900000000001
zeta_station_pv	3,61	0.6620900000000001
zeta_station_pv	4,61	0.6620900000000001
zeta_station_pv	5,61	0.6620900000000001
zeta_station_pv	6,61	0.6620900000000001
zeta_station_pv	7,61	0.6620900000000001
zeta_station_pv	8,61	0.6620900000000001
zeta_station_pv	9,61	0.6620900000000001
zeta_station_pv	10,61	0.6620900000000001
zeta_station_pv	11,61	0.6620900000000001
zeta_station_pv	12,61	0.6620900000000001
zeta_station_pv	13,61	0.6620900000000001
zeta_station_pv	14,61	0.6620900000000001
zeta_station_pv	15,61	0.6620900000000001
zeta_station_pv	16,61	0.6620900000000001
zeta_station_pv	17,61	0.6620900000000001
zeta_station_pv	18,61	0.6620900000000001
zeta_station_pv	19,61	0.6620900000000001
zeta_station_pv	20,61	0.6620900000000001
zeta_station_pv	1,62	0.71313
zeta_station_pv	2,62	0.71313
zeta_station_pv	3,62	0.71313
zeta_station_pv	4,62	0.71313
zeta_station_pv	5,62	0.71313
zeta_station_pv	6,62	0.71313
zeta_station_pv	7,62	0.71313
zeta_station_pv	8,62	0.71313
zeta_station_pv	9,62	0.71313
zeta_station_pv	10,62	0.71313
zeta_station_pv	11,62	0.71313
zeta_station_pv	12,62	0.71313
zeta_station_pv	13,62	0.71313
zeta_station_pv	14,62	0.71313
zeta_station_pv	15,62	0.71313
zeta_station_pv	16,62	0.71313
zeta_station_pv	17,62	0.71313
zeta_station_pv	18,62	0.71313
zeta_station_pv	19,62	0.71313
zeta_station_pv	20,62	0.71313
zeta_station_pv	1,63	0.8705400000000001
zeta_station_pv	2,63	0.8705400000000001
zeta_station_pv	3,63	0.8705400000000001
zeta_station_pv	4,63	0.8705400000000001
zeta_station_pv	5,63	0.8705400000000001
zeta_station_pv	6,63	0.8705400000000001
zeta_station_pv	7,63	0.8705400000000001
zeta_station_pv	8,63	0.8705400000000001
zeta_station_pv	9,63	0.8705400000000001
zeta_station_pv	10,63	0.8705400000000001
zeta_station_pv	11,63	0.8705400000000001
zeta_station_pv	12,63	0.8705400000000001
zeta_station_pv	13,63	0.8705400000000001
zeta_station_pv	14,63	0.8705400000000001
zeta_station_pv	15,63	0.8705400000000001
zeta_station_pv	16,63	0.8705400000000001
zeta_station_pv	17,63	0.8705400000000001
zeta_station_pv	18,63	0.8705400000000001
zeta_station_pv	19,63	0.8705400000000001
zeta_station_pv	20,63	0.8705400000000001
zeta_station_pv	1,64	0.913
zeta_station_pv	2,64	0.913
zeta_station_pv	3,64	0.913
zeta_station_pv	4,64	0.913
zeta_station_pv	5,64	0.913
zeta_station_pv	6,64	0.913
zeta_station_pv	7,64	0.913
zeta_station_pv	8,64	0.913
zeta_station_pv	9,64	0.913
zeta_station_pv	10,64	0.913
zeta_station_pv	11,64	0.913
zeta_station_pv	12,64	0.913
zeta_station_pv	13,64	0.913
zeta_station_pv	14,64	0.913
zeta_station_pv	15,64	0.913
zeta_station_pv	16,64	0.913
zeta_station_pv	17,64	0.913
zeta_station_pv	18,64	0.913
zeta_station_pv	19,64	0.913
zeta_station_pv	20,64	0.913
zeta_station_pv	1,65	0.8869300000000001
zeta_station_pv	2,65	0.8869300000000001
zeta_station_pv	3,65	0.8869300000000001
zeta_station_pv	4,65	0.8869300000000001
zeta_station_pv	5,65	0.8869300000000001
zeta_station_pv	6,65	0.8869300000000001
zeta_station_pv	7,65	0.8869300000000001
zeta_station_pv	8,65	0.8869300000000001
zeta_station_pv	9,65	0.8869300000000001
zeta_station_pv	10,65	0.8869300000000001
zeta_station_pv	11,65	0.8869300000000001
zeta_station_pv	12,65	0.8869300000000001
zeta_station_pv	13,65	0.8869300000000001
zeta_station_pv	14,65	0.8869300000000001
zeta_station_pv	15,65	0.8869300000000001
zeta_station_pv	16,65	0.8869300000000001
zeta_station_pv	17,65	0.8869300000000001
zeta_station_pv	18,65	0.8869300000000001
zeta_station_pv	19,65	0.8869300000000001
zeta_station_pv	20,65	0.8869300000000001
zeta_station_pv	1,66	0.9620600000000001
zeta_station_pv	2,66	0.9620600000000001
zeta_station_pv	3,66	0.9620600000000001
zeta_station_pv	4,66	0.9620600000000001
zeta_station_pv	5,66	0.9620600000000001
zeta_station_pv	6,66	0.9620600000000001
zeta_station_pv	7,66	0.9620600000000001
zeta_station_pv	8,66	0.9620600000000001
zeta_station_pv	9,66	0.9620600000000001
zeta_station_pv	10,66	0.9620600000000001
zeta_station_pv	11,66	0.9620600000000001
zeta_station_pv	12,66	0.9620600000000001
zeta_station_pv	13,66	0.9620600000000001
zeta_station_pv	14,66	0.9620600000000001
zeta_station_pv	15,66	0.9620600000000001
zeta_station_pv	16,66	0.9620600000000001
zeta_station_pv	17,66	0.9620600000000001
zeta_station_pv	18,66	0.9620600000000001
zeta_station_pv	19,66	0.9620600000000001
zeta_station_pv	20,66	0.9620600000000001
zeta_station_pv	1,67	0.62975
zeta_station_pv	2,67	0.62975
zeta_station_pv	3,67	0.62975
zeta_station_pv	4,67	0.62975
zeta_station_pv	5,67	0.62975
zeta_station_pv	6,67	0.62975
zeta_station_pv	7,67	0.62975
zeta_station_pv	8,67	0.62975
zeta_station_pv	9,67	0.62975
zeta_station_pv	10,67	0.62975
zeta_station_pv	11,67	0.62975
zeta_station_pv	12,67	0.62975
zeta_station_pv	13,67	0.62975
zeta_station_pv	14,67	0.62975
zeta_station_pv	15,67	0.62975
zeta_station_pv	16,67	0.62975
zeta_station_pv	17,67	0.62975
zeta_station_pv	18,67	0.62975
zeta_station_pv	19,67	0.62975
zeta_station_pv	20,67	0.62975
zeta_station_pv	1,68	0.40271
zeta_station_pv	2,68	0.40271
zeta_station_pv	3,68	0.40271
zeta_station_pv	4,68	0.40271
zeta_station_pv	5,68	0.40271
zeta_station_pv	6,68	0.40271
zeta_station_pv	7,68	0.40271
zeta_station_pv	8,68	0.40271
zeta_station_pv	9,68	0.40271
zeta_station_pv	10,68	0.40271
zeta_station_pv	11,68	0.40271
zeta_station_pv	12,68	0.40271
zeta_station_pv	13,68	0.40271
zeta_station_pv	14,68	0.40271
zeta_station_pv	15,68	0.40271
zeta_station_pv	16,68	0.40271
zeta_station_pv	17,68	0.40271
zeta_station_pv	18,68	0.40271
zeta_station_pv	19,68	0.40271
zeta_station_pv	20,68	0.40271
zeta_station_pv	1,69	0.0
zeta_station_pv	2,69	0.0
zeta_station_pv	3,69	0.0
zeta_station_pv	4,69	0.0
zeta_station_pv	5,69	0.0
zeta_station_pv	6,69	0.0
zeta_station_pv	7,69	0.0
zeta_station_pv	8,69	0.0
zeta_station_pv	9,69	0.0
zeta_station_pv	10,69	0.0
zeta_station_pv	11,69	0.0
zeta_station_pv	12,69	0.0
zeta_station_pv	13,69	0.0
zeta_station_pv	14,69	0.0
zeta_station_pv	15,69	0.0
zeta_station_pv	16,69	0.0
zeta_station_pv	17,69	0.0
zeta_station_pv	18,69	0.0
zeta_station_pv	19,69	0.0
zeta_station_pv	20,69	0.0
zeta_station_pv	1,70	0.0
zeta_station_pv	2,70	0.0
zeta_station_pv	3,70	0.0
zeta_station_pv	4,70	0.0
zeta_station_pv	5,70	0.0
zeta_station_pv	6,70	0.0
zeta_station_pv	7,70	0.0
zeta_station_pv	8,70	0.0
zeta_station_pv	9,70	0.0
zeta_station_pv	10,70	0.0
zeta_station_pv	11,70	0.0
zeta_station_pv	12,70	0.0
zeta_station_pv	13,70	0.0
zeta_station_pv	14,70	0.0
zeta_station_pv	15,70	0.0
zeta_station_pv	16,70	0.0
zeta_station_pv	17,70	0.0
zeta_station_pv	18,70	0.0
zeta_station_pv	19,70	0.0
zeta_station_pv	20,70	0.0
zeta_station_pv	1,71	0.0
zeta_station_pv	2,71	0.0
zeta_station_pv	3,71	0.0
zeta_station_pv	4,71	0.0
zeta_station_pv	5,71	0.0
zeta_station_pv	6,71	0.0
zeta_station_pv	7,71	0.0
zeta_station_pv	8,71	0.0
zeta_station_pv	9,71	0.0
zeta_station_pv	10,71	0.0
zeta_station_pv	11,71	0.0
zeta_station_pv	12,71	0.0
zeta_station_pv	13,71	0.0
zeta_station_pv	14,71	0.0
zeta_station_pv	15,71	0.0
zeta_station_pv	16,71	0.0
zeta_station_pv	17,71	0.0
zeta_station_pv	18,71	0.0
zeta_station_pv	19,71	0.0
zeta_station_pv	20,71	0.0
zeta_station_pv	1,72	0.0
zeta_station_pv	2,72	0.0
zeta_station_pv	3,72	0.0
zeta_station_pv	4,72	0.0
zeta_station_pv	5,72	0.0
zeta_station_pv	6,72	0.0
zeta_station_pv	7,72	0.0
zeta_station_pv	8,72	0.0
zeta_station_pv	9,72	0.0
zeta_station_pv	10,72	0.0
zeta_station_pv	11,72	0.0
zeta_station_pv	12,72	0.0
zeta_station_pv	13,72	0.0
zeta_station_pv	14,72	0.0
zeta_station_pv	15,72	0.0
zeta_station_pv	16,72	0.0
zeta_station_pv	17,72	0.0
zeta_station_pv	18,72	0.0
zeta_station_pv	19,72	0.0
zeta_station_pv	20,72	0.0
zeta_station_pv	1,73	0.0
zeta_station_pv	2,73	0.0
zeta_station_pv	3,73	0.0
zeta_station_pv	4,73	0.0
zeta_station_pv	5,73	0.0
zeta_station_pv	6,73	0.0
zeta_station_pv	7,73	0.0
zeta_station_pv	8,73	0.0
zeta_station_pv	9,73	0.0
zeta_station_pv	10,73	0.0
zeta_station_pv	11,73	0.0
zeta_station_pv	12,73	0.0
zeta_station_pv	13,73	0.0
zeta_station_pv	14,73	0.0
zeta_station_pv	15,73	0.0
zeta_station_pv	16,73	0.0
zeta_station_pv	17,73	0.0
zeta_station_pv	18,73	0.0
zeta_station_pv	19,73	0.0
zeta_station_pv	20,73	0.0
zeta_station_pv	1,74	0.0
zeta_station_pv	2,74	0.0
zeta_station_pv	3,74	0.0
zeta_station_pv	4,74	0.0
zeta_station_pv	5,74	0.0
zeta_station_pv	6,74	0.0
zeta_station_pv	7,74	0.0
zeta_station_pv	8,74	0.0
zeta_station_pv	9,74	0.0
zeta_station_pv	10,74	0.0
zeta_station_pv	11,74	0.0
zeta_station_pv	12,74	0.0
zeta_station_pv	13,74	0.0
zeta_station_pv	14,74	0.0
zeta_station_pv	15,74	0.0
zeta_station_pv	16,74	0.0
zeta_station_pv	17,74	0.0
zeta_station_pv	18,74	0.0
zeta_station_pv	19,74	0.0
zeta_station_pv	20,74	0.0
zeta_station_pv	1,75	0.0
zeta_station_pv	2,75	0.0
zeta_station_pv	3,75	0.0
zeta_station_pv	4,75	0.0
zeta_station_pv	5,75	0.0
zeta_station_pv	6,75	0.0
zeta_station_pv	7,75	0.0
zeta_station_pv	8,75	0.0
zeta_station_pv	9,75	0.0
zeta_station_pv	10,75	0.0
zeta_station_pv	11,75	0.0
zeta_station_pv	12,75	0.0
zeta_station_pv	13,75	0.0
zeta_station_pv	14,75	0.0
zeta_station_pv	15,75	0.0
zeta_station_pv	16,75	0.0
zeta_station_pv	17,75	0.0
zeta_station_pv	18,75	0.0
zeta_station_pv	19,75	0.0
zeta_station_pv	20,75	0.0
zeta_station_pv	1,76	0.0
zeta_station_pv	2,76	0.0
zeta_station_pv	3,76	0.0
zeta_station_pv	4,76	0.0
zeta_station_pv	5,76	0.0
zeta_station_pv	6,76	0.0
zeta_station_pv	7,76	0.0
zeta_station_pv	8,76	0.0
zeta_station_pv	9,76	0.0
zeta_station_pv	10,76	0.0
zeta_station_pv	11,76	0.0
zeta_station_pv	12,76	0.0
zeta_station_pv	13,76	0.0
zeta_station_pv	14,76	0.0
zeta_station_pv	15,76	0.0
zeta_station_pv	16,76	0.0
zeta_station_pv	17,76	0.0
zeta_station_pv	18,76	0.0
zeta_station_pv	19,76	0.0
zeta_station_pv	20,76	0.0
zeta_station_pv	1,77	0.0
zeta_station_pv	2,77	0.0
zeta_station_pv	3,77	0.0
zeta_station_pv	4,77	0.0
zeta_station_pv	5,77	0.0
zeta_station_pv	6,77	0.0
zeta_station_pv	7,77	0.0
zeta_station_pv	8,77	0.0
zeta_station_pv	9,77	0.0
zeta_station_pv	10,77	0.0
zeta_station_pv	11,77	0.0
zeta_station_pv	12,77	0.0
zeta_station_pv	13,77	0.0
zeta_station_pv	14,77	0.0
zeta_station_pv	15,77	0.0
zeta_station_pv	16,77	0.0
zeta_station_pv	17,77	0.0
zeta_station_pv	18,77	0.0
zeta_station_pv	19,77	0.0
zeta_station_pv	20,77	0.0
zeta_station_pv	1,78	0.0
zeta_station_pv	2,78	0.0
zeta_station_pv	3,78	0.0
zeta_station_pv	4,78	0.0
zeta_station_pv	5,78	0.0
zeta_station_pv	6,78	0.0
zeta_station_pv	7,78	0.0
zeta_station_pv	8,78	0.0
zeta_station_pv	9,78	0.0
zeta_station_pv	10,78	0.0
zeta_station_pv	11,78	0.0
zeta_station_pv	12,78	0.0
zeta_station_pv	13,78	0.0
zeta_station_pv	14,78	0.0
zeta_station_pv	15,78	0.0
zeta_station_pv	16,78	0.0
zeta_station_pv	17,78	0.0
zeta_station_pv	18,78	0.0
zeta_station_pv	19,78	0.0
zeta_station_pv	20,78	0.0
zeta_station_pv	1,79	0.16467
zeta_station_pv	2,79	0.16467
zeta_station_pv	3,79	0.16467
zeta_station_pv	4,79	0.16467
zeta_station_pv	5,79	0.16467
zeta_station_pv	6,79	0.16467
zeta_station_pv	7,79	0.16467
zeta_station_pv	8,79	0.16467
zeta_station_pv	9,79	0.16467
zeta_station_pv	10,79	0.16467
zeta_station_pv	11,79	0.16467
zeta_station_pv	12,79	0.16467
zeta_station_pv	13,79	0.16467
zeta_station_pv	14,79	0.16467
zeta_station_pv	15,79	0.16467
zeta_station_pv	16,79	0.16467
zeta_station_pv	17,79	0.16467
zeta_station_pv	18,79	0.16467
zeta_station_pv	19,79	0.16467
zeta_station_pv	20,79	0.16467
zeta_station_pv	1,80	0.49181
zeta_station_pv	2,80	0.49181
zeta_station_pv	3,80	0.49181
zeta_station_pv	4,80	0.49181
zeta_station_pv	5,80	0.49181
zeta_station_pv	6,80	0.49181
zeta_station_pv	7,80	0.49181
zeta_station_pv	8,80	0.49181
zeta_station_pv	9,80	0.49181
zeta_station_pv	10,80	0.49181
zeta_station_pv	11,80	0.49181
zeta_station_pv	12,80	0.49181
zeta_station_pv	13,80	0.49181
zeta_station_pv	14,80	0.49181
zeta_station_pv	15,80	0.49181
zeta_station_pv	16,80	0.49181
zeta_station_pv	17,80	0.49181
zeta_station_pv	18,80	0.49181
zeta_station_pv	19,80	0.49181
zeta_station_pv	20,80	0.49181
zeta_station_pv	1,81	0.87175
zeta_station_pv	2,81	0.87175
zeta_station_pv	3,81	0.87175
zeta_station_pv	4,81	0.87175
zeta_station_pv	5,81	0.87175
zeta_station_pv	6,81	0.87175
zeta_station_pv	7,81	0.87175
zeta_station_pv	8,81	0.87175
zeta_station_pv	9,81	0.87175
zeta_station_pv	10,81	0.87175
zeta_station_pv	11,81	0.87175
zeta_station_pv	12,81	0.87175
zeta_station_pv	13,81	0.87175
zeta_station_pv	14,81	0.87175
zeta_station_pv	15,81	0.87175
zeta_station_pv	16,81	0.87175
zeta_station_pv	17,81	0.87175
zeta_station_pv	18,81	0.87175
zeta_station_pv	19,81	0.87175
zeta_station_pv	20,81	0.87175
zeta_station_pv	1,82	0.8922100000000002
zeta_station_pv	2,82	0.8922100000000002
zeta_station_pv	3,82	0.8922100000000002
zeta_station_pv	4,82	0.8922100000000002
zeta_station_pv	5,82	0.8922100000000002
zeta_station_pv	6,82	0.8922100000000002
zeta_station_pv	7,82	0.8922100000000002
zeta_station_pv	8,82	0.8922100000000002
zeta_station_pv	9,82	0.8922100000000002
zeta_station_pv	10,82	0.8922100000000002
zeta_station_pv	11,82	0.8922100000000002
zeta_station_pv	12,82	0.8922100000000002
zeta_station_pv	13,82	0.8922100000000002
zeta_station_pv	14,82	0.8922100000000002
zeta_station_pv	15,82	0.8922100000000002
zeta_station_pv	16,82	0.8922100000000002
zeta_station_pv	17,82	0.8922100000000002
zeta_station_pv	18,82	0.8922100000000002
zeta_station_pv	19,82	0.8922100000000002
zeta_station_pv	20,82	0.8922100000000002
zeta_station_pv	1,83	0.8855000000000002
zeta_station_pv	2,83	0.8855000000000002
zeta_station_pv	3,83	0.8855000000000002
zeta_station_pv	4,83	0.8855000000000002
zeta_station_pv	5,83	0.8855000000000002
zeta_station_pv	6,83	0.8855000000000002
zeta_station_pv	7,83	0.8855000000000002
zeta_station_pv	8,83	0.8855000000000002
zeta_station_pv	9,83	0.8855000000000002
zeta_station_pv	10,83	0.8855000000000002
zeta_station_pv	11,83	0.8855000000000002
zeta_station_pv	12,83	0.8855000000000002
zeta_station_pv	13,83	0.8855000000000002
zeta_station_pv	14,83	0.8855000000000002
zeta_station_pv	15,83	0.8855000000000002
zeta_station_pv	16,83	0.8855000000000002
zeta_station_pv	17,83	0.8855000000000002
zeta_station_pv	18,83	0.8855000000000002
zeta_station_pv	19,83	0.8855000000000002
zeta_station_pv	20,83	0.8855000000000002
zeta_station_pv	1,84	0.59917
zeta_station_pv	2,84	0.59917
zeta_station_pv	3,84	0.59917
zeta_station_pv	4,84	0.59917
zeta_station_pv	5,84	0.59917
zeta_station_pv	6,84	0.59917
zeta_station_pv	7,84	0.59917
zeta_station_pv	8,84	0.59917
zeta_station_pv	9,84	0.59917
zeta_station_pv	10,84	0.59917
zeta_station_pv	11,84	0.59917
zeta_station_pv	12,84	0.59917
zeta_station_pv	13,84	0.59917
zeta_station_pv	14,84	0.59917
zeta_station_pv	15,84	0.59917
zeta_station_pv	16,84	0.59917
zeta_station_pv	17,84	0.59917
zeta_station_pv	18,84	0.59917
zeta_station_pv	19,84	0.59917
zeta_station_pv	20,84	0.59917
zeta_station_pv	1,85	0.72369
zeta_station_pv	2,85	0.72369
zeta_station_pv	3,85	0.72369
zeta_station_pv	4,85	0.72369
zeta_station_pv	5,85	0.72369
zeta_station_pv	6,85	0.72369
zeta_station_pv	7,85	0.72369
zeta_station_pv	8,85	0.72369
zeta_station_pv	9,85	0.72369
zeta_station_pv	10,85	0.72369
zeta_station_pv	11,85	0.72369
zeta_station_pv	12,85	0.72369
zeta_station_pv	13,85	0.72369
zeta_station_pv	14,85	0.72369
zeta_station_pv	15,85	0.72369
zeta_station_pv	16,85	0.72369
zeta_station_pv	17,85	0.72369
zeta_station_pv	18,85	0.72369
zeta_station_pv	19,85	0.72369
zeta_station_pv	20,85	0.72369
zeta_station_pv	1,86	0.7103800000000001
zeta_station_pv	2,86	0.7103800000000001
zeta_station_pv	3,86	0.7103800000000001
zeta_station_pv	4,86	0.7103800000000001
zeta_station_pv	5,86	0.7103800000000001
zeta_station_pv	6,86	0.7103800000000001
zeta_station_pv	7,86	0.7103800000000001
zeta_station_pv	8,86	0.7103800000000001
zeta_station_pv	9,86	0.7103800000000001
zeta_station_pv	10,86	0.7103800000000001
zeta_station_pv	11,86	0.7103800000000001
zeta_station_pv	12,86	0.7103800000000001
zeta_station_pv	13,86	0.7103800000000001
zeta_station_pv	14,86	0.7103800000000001
zeta_station_pv	15,86	0.7103800000000001
zeta_station_pv	16,86	0.7103800000000001
zeta_station_pv	17,86	0.7103800000000001
zeta_station_pv	18,86	0.7103800000000001
zeta_station_pv	19,86	0.7103800000000001
zeta_station_pv	20,86	0.7103800000000001
zeta_station_pv	1,87	1.1
zeta_station_pv	2,87	1.1
zeta_station_pv	3,87	1.1
zeta_station_pv	4,87	1.1
zeta_station_pv	5,87	1.1
zeta_station_pv	6,87	1.1
zeta_station_pv	7,87	1.1
zeta_station_pv	8,87	1.1
zeta_station_pv	9,87	1.1
zeta_station_pv	10,87	1.1
zeta_station_pv	11,87	1.1
zeta_station_pv	12,87	1.1
zeta_station_pv	13,87	1.1
zeta_station_pv	14,87	1.1
zeta_station_pv	15,87	1.1
zeta_station_pv	16,87	1.1
zeta_station_pv	17,87	1.1
zeta_station_pv	18,87	1.1
zeta_station_pv	19,87	1.1
zeta_station_pv	20,87	1.1
zeta_station_pv	1,88	0.91498
zeta_station_pv	2,88	0.91498
zeta_station_pv	3,88	0.91498
zeta_station_pv	4,88	0.91498
zeta_station_pv	5,88	0.91498
zeta_station_pv	6,88	0.91498
zeta_station_pv	7,88	0.91498
zeta_station_pv	8,88	0.91498
zeta_station_pv	9,88	0.91498
zeta_station_pv	10,88	0.91498
zeta_station_pv	11,88	0.91498
zeta_station_pv	12,88	0.91498
zeta_station_pv	13,88	0.91498
zeta_station_pv	14,88	0.91498
zeta_station_pv	15,88	0.91498
zeta_station_pv	16,88	0.91498
zeta_station_pv	17,88	0.91498
zeta_station_pv	18,88	0.91498
zeta_station_pv	19,88	0.91498
zeta_station_pv	20,88	0.91498
zeta_station_pv	1,89	1.05952
zeta_station_pv	2,89	1.05952
zeta_station_pv	3,89	1.05952
zeta_station_pv	4,89	1.05952
zeta_station_pv	5,89	1.05952
zeta_station_pv	6,89	1.05952
zeta_station_pv	7,89	1.05952
zeta_station_pv	8,89	1.05952
zeta_station_pv	9,89	1.05952
zeta_station_pv	10,89	1.05952
zeta_station_pv	11,89	1.05952
zeta_station_pv	12,89	1.05952
zeta_station_pv	13,89	1.05952
zeta_station_pv	14,89	1.05952
zeta_station_pv	15,89	1.05952
zeta_station_pv	16,89	1.05952
zeta_station_pv	17,89	1.05952
zeta_station_pv	18,89	1.05952
zeta_station_pv	19,89	1.05952
zeta_station_pv	20,89	1.05952
zeta_station_pv	1,90	0.8474400000000001
zeta_station_pv	2,90	0.8474400000000001
zeta_station_pv	3,90	0.8474400000000001
zeta_station_pv	4,90	0.8474400000000001
zeta_station_pv	5,90	0.8474400000000001
zeta_station_pv	6,90	0.8474400000000001
zeta_station_pv	7,90	0.8474400000000001
zeta_station_pv	8,90	0.8474400000000001
zeta_station_pv	9,90	0.8474400000000001
zeta_station_pv	10,90	0.8474400000000001
zeta_station_pv	11,90	0.8474400000000001
zeta_station_pv	12,90	0.8474400000000001
zeta_station_pv	13,90	0.8474400000000001
zeta_station_pv	14,90	0.8474400000000001
zeta_station_pv	15,90	0.8474400000000001
zeta_station_pv	16,90	0.8474400000000001
zeta_station_pv	17,90	0.8474400000000001
zeta_station_pv	18,90	0.8474400000000001
zeta_station_pv	19,90	0.8474400000000001
zeta_station_pv	20,90	0.8474400000000001
zeta_station_pv	1,91	0.5574800000000001
zeta_station_pv	2,91	0.5574800000000001
zeta_station_pv	3,91	0.5574800000000001
zeta_station_pv	4,91	0.5574800000000001
zeta_station_pv	5,91	0.5574800000000001
zeta_station_pv	6,91	0.5574800000000001
zeta_station_pv	7,91	0.5574800000000001
zeta_station_pv	8,91	0.5574800000000001
zeta_station_pv	9,91	0.5574800000000001
zeta_station_pv	10,91	0.5574800000000001
zeta_station_pv	11,91	0.5574800000000001
zeta_station_pv	12,91	0.5574800000000001
zeta_station_pv	13,91	0.5574800000000001
zeta_station_pv	14,91	0.5574800000000001
zeta_station_pv	15,91	0.5574800000000001
zeta_station_pv	16,91	0.5574800000000001
zeta_station_pv	17,91	0.5574800000000001
zeta_station_pv	18,91	0.5574800000000001
zeta_station_pv	19,91	0.5574800000000001
zeta_station_pv	20,91	0.5574800000000001
zeta_station_pv	1,92	0.36201000000000005
zeta_station_pv	2,92	0.36201000000000005
zeta_station_pv	3,92	0.36201000000000005
zeta_station_pv	4,92	0.36201000000000005
zeta_station_pv	5,92	0.36201000000000005
zeta_station_pv	6,92	0.36201000000000005
zeta_station_pv	7,92	0.36201000000000005
zeta_station_pv	8,92	0.36201000000000005
zeta_station_pv	9,92	0.36201000000000005
zeta_station_pv	10,92	0.36201000000000005
zeta_station_pv	11,92	0.36201000000000005
zeta_station_pv	12,92	0.36201000000000005
zeta_station_pv	13,92	0.36201000000000005
zeta_station_pv	14,92	0.36201000000000005
zeta_station_pv	15,92	0.36201000000000005
zeta_station_pv	16,92	0.36201000000000005
zeta_station_pv	17,92	0.36201000000000005
zeta_station_pv	18,92	0.36201000000000005
zeta_station_pv	19,92	0.36201000000000005
zeta_station_pv	20,92	0.36201000000000005
zeta_station_pv	1,93	0.0
zeta_station_pv	2,93	0.0
zeta_station_pv	3,93	0.0
zeta_station_pv	4,93	0.0
zeta_station_pv	5,93	0.0
zeta_station_pv	6,93	0.0
zeta_station_pv	7,93	0.0
zeta_station_pv	8,93	0.0
zeta_station_pv	9,93	0.0
zeta_station_pv	10,93	0.0
zeta_station_pv	11,93	0.0
zeta_station_pv	12,93	0.0
zeta_station_pv	13,93	0.0
zeta_station_pv	14,93	0.0
zeta_station_pv	15,93	0.0
zeta_station_pv	16,93	0.0
zeta_station_pv	17,93	0.0
zeta_station_pv	18,93	0.0
zeta_station_pv	19,93	0.0
zeta_station_pv	20,93	0.0
zeta_station_pv	1,94	0.0
zeta_station_pv	2,94	0.0
zeta_station_pv	3,94	0.0
zeta_station_pv	4,94	0.0
zeta_station_pv	5,94	0.0
zeta_station_pv	6,94	0.0
zeta_station_pv	7,94	0.0
zeta_station_pv	8,94	0.0
zeta_station_pv	9,94	0.0
zeta_station_pv	10,94	0.0
zeta_station_pv	11,94	0.0
zeta_station_pv	12,94	0.0
zeta_station_pv	13,94	0.0
zeta_station_pv	14,94	0.0
zeta_station_pv	15,94	0.0
zeta_station_pv	16,94	0.0
zeta_station_pv	17,94	0.0
zeta_station_pv	18,94	0.0
zeta_station_pv	19,94	0.0
zeta_station_pv	20,94	0.0
zeta_station_pv	1,95	0.0
zeta_station_pv	2,95	0.0
zeta_station_pv	3,95	0.0
zeta_station_pv	4,95	0.0
zeta_station_pv	5,95	0.0
zeta_station_pv	6,95	0.0
zeta_station_pv	7,95	0.0
zeta_station_pv	8,95	0.0
zeta_station_pv	9,95	0.0
zeta_station_pv	10,95	0.0
zeta_station_pv	11,95	0.0
zeta_station_pv	12,95	0.0
zeta_station_pv	13,95	0.0
zeta_station_pv	14,95	0.0
zeta_station_pv	15,95	0.0
zeta_station_pv	16,95	0.0
zeta_station_pv	17,95	0.0
zeta_station_pv	18,95	0.0
zeta_station_pv	19,95	0.0
zeta_station_pv	20,95	0.0
zeta_station_pv	1,96	0.0
zeta_station_pv	2,96	0.0
zeta_station_pv	3,96	0.0
zeta_station_pv	4,96	0.0
zeta_station_pv	5,96	0.0
zeta_station_pv	6,96	0.0
zeta_station_pv	7,96	0.0
zeta_station_pv	8,96	0.0
zeta_station_pv	9,96	0.0
zeta_station_pv	10,96	0.0
zeta_station_pv	11,96	0.0
zeta_station_pv	12,96	0.0
zeta_station_pv	13,96	0.0
zeta_station_pv	14,96	0.0
zeta_station_pv	15,96	0.0
zeta_station_pv	16,96	0.0
zeta_station_pv	17,96	0.0
zeta_station_pv	18,96	0.0
zeta_station_pv	19,96	0.0
zeta_station_pv	20,96	0.0
zeta_t	scalar	1.0
""")
    resource20("checkpoint/FIX17_NATIVE_PRODUCTION.csv","0475240b92f748301593da4e0d998b9e206f7893fbe57cd339c5a6fed5613fba","""branch,stage,scope,predecessor_sha256,seed_scenario_sha256,initial_inner_feasible,initial_inner_termination,initial_inner_primal,initial_inner_variables,initial_inner_constraints,initial_column_count,integer_variable_count,production_symbolic_master_method_file,production_symbolic_master_method_line,production_symbolic_master_executed,uncertainty_factory_calls,symbolic_builder_calls,uncertainty_binary_count,domain_cardinality,full_domain_symbolic,production_farkas_master_attempted,production_farkas_master_solved,farkas_master_variables,farkas_master_constraints,farkas_master_termination,farkas_master_primal,farkas_master_incumbent,farkas_master_bound,farkas_gate,native_history_phase,native_result_reason,production_extract_f_executed,extract_factory_call,extracted_scenario_valid,extracted_scenario_sha256,scenario_replay_attempted,next_inner_termination,next_inner_primal,next_inner_feasible,next_inner_lower_bound,next_inner_incumbent,next_inner_hamming_from_farkas_column,root_cut_added,global_cut_added,other_patterns_excluded,full_phi3_certified
\"paper_zero\",\"3\",\"REVCS finite-resolution cost-to-go / 397064107615c46ecc08f6cb5c948de814fcda707ced93a390f990e6fd4abec1\",\"3c66893748c4b19be962a1b8e4fc5bcbec26797db02b2833ffdfbb990112ce4a\",\"b1f3fa0e7096e84061acdbba7762174fd4cd0de33cc177653dbf92c589e97887\",\"true\",\"TIME_LIMIT\",\"FEASIBLE_POINT\",\"75481\",\"153238\",\"1\",\"4180\",\"REVCS19_G7_4_2_FIX18_SIGN_AWARE_PRODUCTION.jl\",\"13\",\"true\",\"2\",\"1\",\"3764\",\"8753895993947794718433610778626330373247778063767901123630634050160037560396810629969739308388342200936898700335257040462715069810566046285971964549791645647970820532453935396458981478039318470856114157839872461140075552704143034135376515338324739287246872728532251810199218526604391165934815730949689123984575139077310875335035431289108269929323153416595082253223183749780693180611992086840586052469764407481942653107631394014711014959459611926488656514775466619642431496765638310790137588782760752381642133289627449518674554438427904352679037439013561379176556668707889269064620867591017209665600244570348319217302822818743899476861440956333601871464254592675885490935359155085407263732573805824283864556182195814354113721786118827704986029737712136958718694515633170625177730938924618774140753746995938552523206297657383259158096775240975012402560039593495328027348759356455249594746890782642409\",\"true\",\"true\",\"true\",\"217591\",\"612826\",\"TIME_LIMIT\",\"FEASIBLE_POINT\",\"4.9063606557377\",\"1.7343791965885705e6\",\"witness\",\"feasibility\",\"iteration_limit\",\"true\",\"1\",\"true\",\"87a5aee2a9565d69eea8c1dede66f35c8fc54d4003d367ceac3b98f2bb8d6827\",\"true\",\"TIME_LIMIT\",\"FEASIBLE_POINT\",\"true\",\"1.1786101129069915e6\",\"1.2309076446586617e6\",\"415\",\"false\",\"false\",\"false\",\"false\"
""")
    resource20("checkpoint/FIX17_NEXT_INNER_INTEGER_PATTERN.tsv","6ee00584262f26eb9e2f749a0be640956b315300ea4dbdebbc5715769a82affa","""variable_index	value
1	1
2	0
3	1
4	0
5	0
6	0
7	0
8	1
9	1
10	1
11	0
12	0
13	0
14	1
15	0
16	1
17	1
18	0
19	0
20	1
21	0
22	0
23	0
24	0
25	0
26	0
27	0
28	0
29	0
30	0
31	0
32	0
33	0
34	0
35	0
36	0
37	0
38	0
39	0
40	0
41	1
42	0
43	1
44	0
45	0
46	0
47	0
48	1
49	1
50	1
51	0
52	0
53	0
54	1
55	0
56	1
57	1
58	0
59	0
60	1
61	1
62	0
63	1
64	0
65	0
66	0
67	0
68	1
69	1
70	1
71	0
72	0
73	0
74	1
75	0
76	1
77	1
78	0
79	0
80	1
81	1
82	0
83	1
84	0
85	0
86	0
87	0
88	1
89	1
90	1
91	0
92	0
93	0
94	1
95	0
96	1
97	1
98	0
99	0
100	1
281	1
282	0
283	1
284	0
285	0
286	0
287	0
288	1
289	1
290	1
291	0
292	0
293	0
294	1
295	0
296	1
297	1
298	0
299	0
300	1
301	1
302	0
303	1
304	0
305	0
306	0
307	0
308	1
309	1
310	1
311	0
312	0
313	0
314	1
315	0
316	1
317	1
318	0
319	0
320	1
321	1
322	0
323	1
324	0
325	0
326	0
327	0
328	1
329	1
330	1
331	0
332	0
333	0
334	1
335	0
336	1
337	1
338	0
339	0
340	1
341	1
342	0
343	1
344	0
345	0
346	0
347	0
348	1
349	1
350	1
351	0
352	0
353	0
354	1
355	0
356	1
357	1
358	0
359	0
360	1
361	1
362	0
363	0
364	0
365	0
366	0
367	0
368	1
369	0
370	0
371	0
372	0
373	0
374	0
375	0
376	0
377	0
378	0
379	0
380	0
381	1
382	0
383	0
384	0
385	0
386	0
387	0
388	1
389	1
390	1
391	0
392	0
393	0
394	0
395	0
396	1
397	0
398	0
399	0
400	0
401	1
402	0
403	1
404	0
405	0
406	0
407	0
408	1
409	1
410	1
411	0
412	0
413	0
414	1
415	0
416	1
417	1
418	0
419	0
420	1
421	1
422	0
423	1
424	0
425	0
426	0
427	0
428	1
429	1
430	1
431	0
432	0
433	0
434	1
435	0
436	1
437	1
438	0
439	0
440	1
441	1
442	0
443	1
444	0
445	0
446	0
447	0
448	1
449	1
450	1
451	0
452	0
453	0
454	1
455	0
456	1
457	1
458	0
459	0
460	1
461	1
462	0
463	1
464	0
465	0
466	0
467	0
468	1
469	1
470	1
471	0
472	0
473	0
474	1
475	0
476	1
477	1
478	0
479	0
480	1
481	1
482	0
483	1
484	0
485	0
486	0
487	0
488	1
489	1
490	1
491	0
492	0
493	0
494	1
495	0
496	1
497	1
498	0
499	0
500	1
501	0
502	0
503	0
504	0
505	0
506	0
507	0
508	0
509	0
510	1
511	0
512	0
513	0
514	0
515	0
516	1
517	1
518	0
519	0
520	1
521	1
522	0
523	0
524	0
525	0
526	0
527	0
528	1
529	0
530	1
531	0
532	0
533	0
534	0
535	0
536	1
537	1
538	0
539	0
540	1
541	1
542	0
543	1
544	0
545	0
546	0
547	0
548	1
549	1
550	1
551	0
552	0
553	0
554	1
555	0
556	1
557	1
558	0
559	0
560	1
561	1
562	0
563	1
564	0
565	0
566	0
567	0
568	1
569	1
570	1
571	0
572	0
573	0
574	1
575	0
576	1
577	1
578	0
579	0
580	1
581	1
582	0
583	1
584	0
585	0
586	0
587	0
588	1
589	1
590	1
591	0
592	0
593	0
594	1
595	0
596	1
597	1
598	0
599	0
600	1
601	1
602	0
603	1
604	0
605	0
606	0
607	0
608	1
609	1
610	1
611	0
612	0
613	0
614	1
615	0
616	1
617	1
618	0
619	0
620	1
621	1
622	0
623	1
624	0
625	0
626	0
627	0
628	1
629	1
630	1
631	0
632	0
633	0
634	1
635	0
636	1
637	1
638	0
639	0
640	1
641	1
642	0
643	1
644	0
645	0
646	0
647	0
648	1
649	1
650	1
651	0
652	0
653	0
654	1
655	0
656	1
657	1
658	0
659	0
660	1
661	1
662	0
663	1
664	0
665	0
666	0
667	0
668	1
669	1
670	1
671	0
672	0
673	0
674	1
675	0
676	1
677	1
678	0
679	0
680	1
681	1
682	0
683	1
684	0
685	0
686	0
687	0
688	1
689	0
690	0
691	0
692	0
693	0
694	1
695	0
696	1
697	0
698	0
699	0
700	0
701	0
702	0
703	1
704	0
705	0
706	0
707	0
708	0
709	0
710	1
711	0
712	0
713	0
714	1
715	0
716	1
717	1
718	0
719	0
720	1
721	1
722	0
723	1
724	0
725	0
726	0
727	0
728	1
729	1
730	1
731	0
732	0
733	0
734	1
735	0
736	1
737	1
738	0
739	0
740	1
741	1
742	0
743	1
744	0
745	0
746	0
747	0
748	1
749	1
750	1
751	0
752	0
753	0
754	1
755	0
756	1
757	1
758	0
759	0
760	1
761	1
762	0
763	1
764	0
765	0
766	0
767	0
768	1
769	1
770	1
771	0
772	0
773	0
774	1
775	0
776	1
777	1
778	0
779	0
780	1
781	1
782	0
783	1
784	0
785	0
786	0
787	0
788	1
789	1
790	1
791	0
792	0
793	0
794	1
795	0
796	1
797	1
798	0
799	0
800	1
801	1
802	0
803	1
804	0
805	0
806	0
807	0
808	1
809	1
810	1
811	0
812	0
813	0
814	1
815	0
816	1
817	1
818	0
819	0
820	1
821	1
822	0
823	1
824	0
825	0
826	0
827	0
828	1
829	1
830	1
831	0
832	0
833	0
834	1
835	0
836	1
837	1
838	0
839	0
840	1
841	0
842	0
843	0
844	0
845	0
846	0
847	0
848	0
849	1
850	1
851	0
852	0
853	0
854	0
855	0
856	0
857	0
858	0
859	0
860	0
861	1
862	0
863	1
864	0
865	0
866	0
867	0
868	1
869	1
870	1
871	0
872	0
873	0
874	1
875	0
876	0
877	0
878	0
879	0
880	1
881	1
882	0
883	1
884	0
885	0
886	0
887	0
888	1
889	1
890	1
891	0
892	0
893	0
894	1
895	0
896	1
897	1
898	0
899	0
900	1
901	1
902	0
903	1
904	0
905	0
906	0
907	0
908	1
909	1
910	1
911	0
912	0
913	0
914	1
915	0
916	1
917	1
918	0
919	0
920	1
921	1
922	0
923	1
924	0
925	0
926	0
927	0
928	1
929	1
930	1
931	0
932	0
933	0
934	1
935	0
936	1
937	1
938	0
939	0
940	1
941	1
942	0
943	1
944	0
945	0
946	0
947	0
948	1
949	1
950	1
951	0
952	0
953	0
954	1
955	0
956	1
957	1
958	0
959	0
960	1
961	1
962	0
963	1
964	0
965	0
966	0
967	0
968	1
969	1
970	1
971	0
972	0
973	0
974	1
975	0
976	1
977	1
978	0
979	0
980	1
981	0
982	0
983	0
984	0
985	0
986	0
987	0
988	0
989	0
990	1
991	0
992	0
993	0
994	1
995	0
996	0
997	0
998	0
999	0
1000	0
1001	0
1002	0
1003	1
1004	0
1005	0
1006	0
1007	0
1008	0
1009	0
1010	1
1011	0
1012	0
1013	0
1014	1
1015	0
1016	0
1017	0
1018	0
1019	0
1020	1
1021	1
1022	0
1023	1
1024	0
1025	0
1026	0
1027	0
1028	1
1029	1
1030	1
1031	0
1032	0
1033	0
1034	1
1035	0
1036	1
1037	1
1038	0
1039	0
1040	1
1041	1
1042	0
1043	1
1044	0
1045	0
1046	0
1047	0
1048	1
1049	1
1050	1
1051	0
1052	0
1053	0
1054	1
1055	0
1056	1
1057	1
1058	0
1059	0
1060	1
1061	1
1062	0
1063	1
1064	0
1065	0
1066	0
1067	0
1068	1
1069	1
1070	1
1071	0
1072	0
1073	0
1074	1
1075	0
1076	1
1077	1
1078	0
1079	0
1080	1
1081	1
1082	0
1083	1
1084	0
1085	0
1086	0
1087	0
1088	1
1089	1
1090	1
1091	0
1092	0
1093	0
1094	1
1095	0
1096	1
1097	1
1098	0
1099	0
1100	1
1101	1
1102	0
1103	1
1104	0
1105	0
1106	0
1107	0
1108	1
1109	1
1110	1
1111	0
1112	0
1113	0
1114	1
1115	0
1116	1
1117	1
1118	0
1119	0
1120	1
1121	1
1122	0
1123	1
1124	0
1125	0
1126	0
1127	0
1128	1
1129	1
1130	1
1131	0
1132	0
1133	0
1134	1
1135	0
1136	1
1137	1
1138	0
1139	0
1140	1
1141	1
1142	0
1143	1
1144	0
1145	0
1146	0
1147	0
1148	1
1149	1
1150	1
1151	0
1152	0
1153	0
1154	1
1155	0
1156	1
1157	1
1158	0
1159	0
1160	1
1161	0
1162	0
1163	1
1164	0
1165	0
1166	0
1167	0
1168	1
1169	0
1170	0
1171	0
1172	0
1173	0
1174	1
1175	0
1176	0
1177	0
1178	0
1179	0
1180	0
1181	1
1182	0
1183	1
1184	0
1185	0
1186	0
1187	0
1188	0
1189	1
1190	1
1191	0
1192	0
1193	0
1194	0
1195	0
1196	1
1197	1
1198	0
1199	0
1200	0
1201	1
1202	0
1203	1
1204	0
1205	0
1206	0
1207	0
1208	1
1209	1
1210	1
1211	0
1212	0
1213	0
1214	1
1215	0
1216	1
1217	1
1218	0
1219	0
1220	1
1221	1
1222	0
1223	1
1224	0
1225	0
1226	0
1227	0
1228	1
1229	1
1230	1
1231	0
1232	0
1233	0
1234	1
1235	0
1236	0
1237	1
1238	0
1239	0
1240	1
1241	1
1242	0
1243	1
1244	0
1245	0
1246	0
1247	0
1248	1
1249	1
1250	1
1251	0
1252	0
1253	0
1254	1
1255	0
1256	1
1257	1
1258	0
1259	0
1260	1
1261	1
1262	0
1263	1
1264	0
1265	0
1266	0
1267	0
1268	1
1269	1
1270	1
1271	0
1272	0
1273	0
1274	1
1275	0
1276	1
1277	1
1278	0
1279	0
1280	1
1281	1
1282	0
1283	1
1284	0
1285	0
1286	0
1287	0
1288	1
1289	1
1290	1
1291	0
1292	0
1293	0
1294	1
1295	0
1296	1
1297	1
1298	0
1299	0
1300	1
1301	1
1302	0
1303	1
1304	0
1305	0
1306	0
1307	0
1308	1
1309	1
1310	1
1311	0
1312	0
1313	0
1314	1
1315	0
1316	1
1317	1
1318	0
1319	0
1320	1
1321	0
1322	0
1323	0
1324	0
1325	0
1326	0
1327	0
1328	0
1329	1
1330	1
1331	0
1332	0
1333	0
1334	1
1335	0
1336	0
1337	0
1338	0
1339	0
1340	0
1341	1
1342	0
1343	1
1344	0
1345	0
1346	0
1347	0
1348	1
1349	1
1350	0
1351	0
1352	0
1353	0
1354	0
1355	0
1356	0
1357	1
1358	0
1359	0
1360	0
1361	1
1362	0
1363	1
1364	0
1365	0
1366	0
1367	0
1368	1
1369	1
1370	1
1371	0
1372	0
1373	0
1374	1
1375	0
1376	1
1377	1
1378	0
1379	0
1380	1
1381	1
1382	0
1383	1
1384	0
1385	0
1386	0
1387	0
1388	1
1389	1
1390	1
1391	0
1392	0
1393	0
1394	1
1395	0
1396	1
1397	1
1398	0
1399	0
1400	1
1401	1
1402	0
1403	1
1404	0
1405	0
1406	0
1407	0
1408	1
1409	0
1410	1
1411	0
1412	0
1413	0
1414	1
1415	0
1416	1
1417	0
1418	0
1419	0
1420	1
1421	1
1422	0
1423	1
1424	0
1425	0
1426	0
1427	0
1428	1
1429	1
1430	1
1431	0
1432	0
1433	0
1434	1
1435	0
1436	1
1437	1
1438	0
1439	0
1440	1
1441	1
1442	0
1443	1
1444	0
1445	0
1446	0
1447	0
1448	1
1449	1
1450	1
1451	0
1452	0
1453	0
1454	1
1455	0
1456	1
1457	1
1458	0
1459	0
1460	1
1461	1
1462	0
1463	1
1464	0
1465	0
1466	0
1467	0
1468	1
1469	1
1470	0
1471	0
1472	0
1473	0
1474	0
1475	0
1476	1
1477	1
1478	0
1479	0
1480	1
1481	1
1482	0
1483	1
1484	0
1485	0
1486	0
1487	0
1488	0
1489	0
1490	1
1491	0
1492	0
1493	0
1494	1
1495	0
1496	1
1497	1
1498	0
1499	0
1500	1
1501	1
1502	0
1503	1
1504	0
1505	0
1506	0
1507	0
1508	1
1509	1
1510	1
1511	0
1512	0
1513	0
1514	1
1515	0
1516	1
1517	1
1518	0
1519	0
1520	1
1521	1
1522	0
1523	1
1524	0
1525	0
1526	0
1527	0
1528	1
1529	1
1530	1
1531	0
1532	0
1533	0
1534	1
1535	0
1536	1
1537	1
1538	0
1539	0
1540	1
1541	1
1542	0
1543	1
1544	0
1545	0
1546	0
1547	0
1548	1
1549	1
1550	1
1551	0
1552	0
1553	0
1554	1
1555	0
1556	1
1557	1
1558	0
1559	0
1560	1
1561	1
1562	0
1563	1
1564	0
1565	0
1566	0
1567	0
1568	1
1569	1
1570	1
1571	0
1572	0
1573	0
1574	1
1575	0
1576	1
1577	1
1578	0
1579	0
1580	1
1581	1
1582	0
1583	1
1584	0
1585	0
1586	0
1587	0
1588	1
1589	1
1590	1
1591	0
1592	0
1593	0
1594	1
1595	0
1596	1
1597	1
1598	0
1599	0
1600	1
1601	1
1602	0
1603	1
1604	0
1605	0
1606	0
1607	0
1608	1
1609	1
1610	1
1611	0
1612	0
1613	0
1614	1
1615	0
1616	1
1617	1
1618	0
1619	0
1620	1
1621	1
1622	0
1623	1
1624	0
1625	0
1626	0
1627	0
1628	1
1629	1
1630	1
1631	0
1632	0
1633	0
1634	1
1635	0
1636	1
1637	1
1638	0
1639	0
1640	1
1641	1
1642	0
1643	0
1644	0
1645	0
1646	0
1647	0
1648	0
1649	1
1650	1
1651	0
1652	0
1653	0
1654	1
1655	0
1656	1
1657	1
1658	0
1659	0
1660	1
1661	1
1662	0
1663	0
1664	0
1665	0
1666	0
1667	0
1668	0
1669	0
1670	1
1671	0
1672	0
1673	0
1674	1
1675	0
1676	1
1677	1
1678	0
1679	0
1680	0
1681	1
1682	0
1683	1
1684	0
1685	0
1686	0
1687	0
1688	1
1689	1
1690	0
1691	0
1692	0
1693	0
1694	1
1695	0
1696	1
1697	1
1698	0
1699	0
1700	1
1701	1
1702	0
1703	1
1704	0
1705	0
1706	0
1707	0
1708	1
1709	1
1710	1
1711	0
1712	0
1713	0
1714	1
1715	0
1716	1
1717	1
1718	0
1719	0
1720	1
1721	1
1722	0
1723	1
1724	0
1725	0
1726	0
1727	0
1728	1
1729	1
1730	1
1731	0
1732	0
1733	0
1734	1
1735	0
1736	1
1737	1
1738	0
1739	0
1740	1
1741	1
1742	0
1743	1
1744	0
1745	0
1746	0
1747	0
1748	0
1749	0
1750	1
1751	0
1752	0
1753	0
1754	1
1755	0
1756	1
1757	1
1758	0
1759	0
1760	0
1761	1
1762	0
1763	1
1764	0
1765	0
1766	0
1767	0
1768	1
1769	1
1770	1
1771	0
1772	0
1773	0
1774	1
1775	0
1776	1
1777	1
1778	0
1779	0
1780	1
1781	1
1782	0
1783	1
1784	0
1785	0
1786	0
1787	0
1788	1
1789	1
1790	1
1791	0
1792	0
1793	0
1794	1
1795	0
1796	1
1797	1
1798	0
1799	0
1800	1
1801	0
1802	0
1803	1
1804	0
1805	0
1806	0
1807	0
1808	0
1809	1
1810	1
1811	0
1812	0
1813	0
1814	1
1815	0
1816	0
1817	1
1818	0
1819	0
1820	1
1821	0
1822	0
1823	0
1824	0
1825	0
1826	0
1827	0
1828	1
1829	1
1830	0
1831	0
1832	0
1833	0
1834	1
1835	0
1836	1
1837	1
1838	0
1839	0
1840	0
1841	1
1842	0
1843	1
1844	0
1845	0
1846	0
1847	0
1848	1
1849	1
1850	1
1851	0
1852	0
1853	0
1854	1
1855	0
1856	1
1857	1
1858	0
1859	0
1860	1
1861	1
1862	0
1863	1
1864	0
1865	0
1866	0
1867	0
1868	1
1869	1
1870	1
1871	0
1872	0
1873	0
1874	1
1875	0
1876	1
1877	1
1878	0
1879	0
1880	1
1881	1
1882	0
1883	1
1884	0
1885	0
1886	0
1887	0
1888	1
1889	1
1890	1
1891	0
1892	0
1893	0
1894	1
1895	0
1896	1
1897	1
1898	0
1899	0
1900	1
1901	1
1902	0
1903	1
1904	0
1905	0
1906	0
1907	0
1908	1
1909	1
1910	1
1911	0
1912	0
1913	0
1914	1
1915	0
1916	1
1917	1
1918	0
1919	0
1920	1
1921	0
1922	0
1923	0
1924	0
1925	0
1926	0
1927	0
1928	0
1929	1
1930	1
1931	0
1932	0
1933	0
1934	1
1935	0
1936	1
1937	0
1938	0
1939	0
1940	1
1941	1
1942	0
1943	1
1944	0
1945	0
1946	0
1947	0
1948	1
1949	1
1950	1
1951	0
1952	0
1953	0
1954	1
1955	0
1956	1
1957	1
1958	0
1959	0
1960	1
1961	1
1962	0
1963	1
1964	0
1965	0
1966	0
1967	0
1968	1
1969	1
1970	1
1971	0
1972	0
1973	0
1974	1
1975	0
1976	1
1977	1
1978	0
1979	0
1980	1
1981	1
1982	0
1983	1
1984	0
1985	0
1986	0
1987	0
1988	1
1989	1
1990	1
1991	0
1992	0
1993	0
1994	1
1995	0
1996	1
1997	1
1998	0
1999	0
2000	1
2001	1
2002	0
2003	1
2004	0
2005	0
2006	0
2007	0
2008	1
2009	1
2010	1
2011	0
2012	0
2013	0
2014	1
2015	0
2016	1
2017	1
2018	0
2019	0
2020	1
2021	1
2022	0
2023	1
2024	0
2025	0
2026	0
2027	0
2028	1
2029	1
2030	1
2031	0
2032	0
2033	0
2034	1
2035	0
2036	1
2037	1
2038	0
2039	0
2040	1
2041	1
2042	0
2043	1
2044	0
2045	0
2046	0
2047	0
2048	1
2049	1
2050	1
2051	0
2052	0
2053	0
2054	1
2055	0
2056	1
2057	1
2058	0
2059	0
2060	1
2061	1
2062	0
2063	1
2064	0
2065	0
2066	0
2067	0
2068	1
2069	1
2070	1
2071	0
2072	0
2073	0
2074	1
2075	0
2076	1
2077	1
2078	0
2079	0
2080	1
2081	1
2082	0
2083	1
2084	0
2085	0
2086	0
2087	0
2088	1
2089	1
2090	1
2091	0
2092	0
2093	0
2094	1
2095	0
2096	1
2097	1
2098	0
2099	0
2100	1
2101	1
2102	0
2103	1
2104	0
2105	0
2106	0
2107	0
2108	1
2109	1
2110	1
2111	0
2112	0
2113	0
2114	1
2115	0
2116	1
2117	1
2118	0
2119	0
2120	1
2121	1
2122	0
2123	0
2124	0
2125	0
2126	0
2127	0
2128	1
2129	1
2130	0
2131	0
2132	0
2133	0
2134	0
2135	0
2136	1
2137	0
2138	0
2139	0
2140	1
2141	1
2142	0
2143	1
2144	0
2145	0
2146	0
2147	0
2148	0
2149	1
2150	0
2151	0
2152	0
2153	0
2154	1
2155	0
2156	1
2157	0
2158	0
2159	0
2160	0
2161	1
2162	0
2163	1
2164	0
2165	0
2166	0
2167	0
2168	1
2169	1
2170	1
2171	0
2172	0
2173	0
2174	1
2175	0
2176	1
2177	1
2178	0
2179	0
2180	1
2181	1
2182	0
2183	1
2184	0
2185	0
2186	0
2187	0
2188	1
2189	1
2190	1
2191	0
2192	0
2193	0
2194	1
2195	0
2196	1
2197	1
2198	0
2199	0
2200	1
2201	0
2202	0
2203	0
2204	0
2205	0
2206	0
2207	0
2208	0
2209	0
2210	0
2211	0
2212	0
2213	0
2214	0
2215	0
2216	0
2217	0
2218	0
2219	0
2220	0
2221	0
2222	0
2223	0
2224	0
2225	0
2226	0
2227	0
2228	0
2229	0
2230	0
2231	0
2232	0
2233	0
2234	0
2235	0
2236	0
2237	0
2238	0
2239	0
2240	0
2241	0
2242	0
2243	0
2244	0
2245	0
2246	0
2247	0
2248	0
2249	0
2250	0
2251	0
2252	0
2253	0
2254	0
2255	0
2256	0
2257	0
2258	0
2259	0
2260	0
2261	0
2262	0
2263	0
2264	0
2265	0
2266	0
2267	0
2268	0
2269	0
2270	0
2271	0
2272	0
2273	0
2274	0
2275	0
2276	0
2277	0
2278	0
2279	0
2280	0
2281	0
2282	0
2283	1
2284	0
2285	0
2286	0
2287	0
2288	0
2289	1
2290	1
2291	0
2292	0
2293	0
2294	1
2295	0
2296	1
2297	1
2298	0
2299	0
2300	1
2301	0
2302	0
2303	1
2304	0
2305	0
2306	0
2307	0
2308	0
2309	0
2310	0
2311	0
2312	0
2313	0
2314	1
2315	0
2316	0
2317	1
2318	0
2319	0
2320	1
2321	0
2322	0
2323	0
2324	0
2325	0
2326	0
2327	0
2328	0
2329	0
2330	0
2331	0
2332	0
2333	0
2334	0
2335	0
2336	0
2337	0
2338	0
2339	0
2340	0
2341	0
2342	0
2343	0
2344	0
2345	0
2346	0
2347	0
2348	0
2349	0
2350	0
2351	0
2352	0
2353	0
2354	0
2355	0
2356	0
2357	0
2358	0
2359	0
2360	0
2361	0
2362	0
2363	0
2364	0
2365	0
2366	0
2367	0
2368	0
2369	0
2370	0
2371	0
2372	0
2373	0
2374	0
2375	0
2376	0
2377	0
2378	0
2379	0
2380	0
2381	0
2382	0
2383	0
2384	0
2385	0
2386	0
2387	0
2388	0
2389	0
2390	0
2391	0
2392	0
2393	0
2394	0
2395	0
2396	0
2397	0
2398	0
2399	0
2400	0
2401	0
2402	0
2403	0
2404	0
2405	0
2406	0
2407	0
2408	0
2409	0
2410	0
2411	0
2412	0
2413	0
2414	0
2415	0
2416	0
2417	0
2418	0
2419	0
2420	0
2421	1
2422	0
2423	1
2424	0
2425	0
2426	0
2427	0
2428	1
2429	1
2430	0
2431	0
2432	0
2433	0
2434	1
2435	0
2436	0
2437	0
2438	0
2439	0
2440	0
2441	0
2442	0
2443	1
2444	0
2445	0
2446	0
2447	0
2448	0
2449	1
2450	0
2451	0
2452	0
2453	0
2454	1
2455	0
2456	0
2457	0
2458	0
2459	0
2460	0
2461	0
2462	0
2463	0
2464	0
2465	0
2466	0
2467	0
2468	0
2469	0
2470	0
2471	0
2472	0
2473	0
2474	0
2475	0
2476	0
2477	0
2478	0
2479	0
2480	0
2481	0
2482	0
2483	0
2484	0
2485	0
2486	0
2487	0
2488	0
2489	0
2490	0
2491	0
2492	0
2493	0
2494	0
2495	0
2496	0
2497	0
2498	0
2499	0
2500	0
2501	0
2502	0
2503	0
2504	0
2505	0
2506	0
2507	0
2508	0
2509	0
2510	0
2511	0
2512	0
2513	0
2514	0
2515	0
2516	0
2517	0
2518	0
2519	0
2520	0
2521	0
2522	0
2523	0
2524	0
2525	0
2526	0
2527	0
2528	0
2529	0
2530	0
2531	0
2532	0
2533	0
2534	0
2535	0
2536	0
2537	0
2538	0
2539	0
2540	0
2541	0
2542	0
2543	0
2544	0
2545	0
2546	0
2547	0
2548	0
2549	0
2550	0
2551	0
2552	0
2553	0
2554	0
2555	0
2556	0
2557	0
2558	0
2559	0
2560	0
2561	0
2562	0
2563	0
2564	0
2565	0
2566	0
2567	0
2568	0
2569	0
2570	0
2571	0
2572	0
2573	0
2574	0
2575	0
2576	0
2577	0
2578	0
2579	0
2580	0
2581	0
2582	0
2583	0
2584	0
2585	0
2586	0
2587	0
2588	0
2589	0
2590	0
2591	0
2592	0
2593	0
2594	0
2595	0
2596	0
2597	0
2598	0
2599	0
2600	0
2601	0
2602	0
2603	0
2604	0
2605	0
2606	0
2607	0
2608	0
2609	1
2610	1
2611	0
2612	0
2613	0
2614	0
2615	0
2616	0
2617	1
2618	0
2619	0
2620	1
2621	1
2622	0
2623	0
2624	0
2625	0
2626	0
2627	0
2628	1
2629	1
2630	0
2631	0
2632	0
2633	0
2634	0
2635	0
2636	0
2637	0
2638	0
2639	0
2640	0
2641	0
2642	0
2643	0
2644	0
2645	0
2646	0
2647	0
2648	0
2649	0
2650	0
2651	0
2652	0
2653	0
2654	0
2655	0
2656	0
2657	0
2658	0
2659	0
2660	0
2661	0
2662	0
2663	0
2664	0
2665	0
2666	0
2667	0
2668	0
2669	0
2670	0
2671	0
2672	0
2673	0
2674	0
2675	0
2676	0
2677	0
2678	0
2679	0
2680	0
2681	0
2682	0
2683	0
2684	0
2685	0
2686	0
2687	0
2688	0
2689	0
2690	0
2691	0
2692	0
2693	0
2694	0
2695	0
2696	0
2697	0
2698	0
2699	0
2700	0
2701	0
2702	0
2703	0
2704	0
2705	0
2706	0
2707	0
2708	0
2709	0
2710	0
2711	0
2712	0
2713	0
2714	0
2715	0
2716	0
2717	0
2718	0
2719	0
2720	0
2721	0
2722	0
2723	0
2724	0
2725	0
2726	0
2727	0
2728	0
2729	0
2730	0
2731	0
2732	0
2733	0
2734	0
2735	0
2736	0
2737	0
2738	0
2739	0
2740	0
2741	0
2742	0
2743	0
2744	0
2745	0
2746	0
2747	0
2748	0
2749	0
2750	0
2751	0
2752	0
2753	0
2754	0
2755	0
2756	0
2757	0
2758	0
2759	0
2760	0
2761	1
2762	0
2763	1
2764	0
2765	0
2766	0
2767	0
2768	1
2769	0
2770	0
2771	0
2772	0
2773	0
2774	1
2775	0
2776	1
2777	1
2778	0
2779	0
2780	1
2781	0
2782	0
2783	0
2784	0
2785	0
2786	0
2787	0
2788	0
2789	0
2790	0
2791	0
2792	0
2793	0
2794	0
2795	0
2796	1
2797	1
2798	0
2799	0
2800	0
2801	0
2802	0
2803	0
2804	0
2805	0
2806	0
2807	0
2808	0
2809	0
2810	0
2811	0
2812	0
2813	0
2814	0
2815	0
2816	0
2817	0
2818	0
2819	0
2820	0
2821	0
2822	0
2823	0
2824	0
2825	0
2826	0
2827	0
2828	0
2829	0
2830	0
2831	0
2832	0
2833	0
2834	0
2835	0
2836	0
2837	0
2838	0
2839	0
2840	0
2841	0
2842	0
2843	0
2844	0
2845	0
2846	0
2847	0
2848	0
2849	0
2850	0
2851	0
2852	0
2853	0
2854	0
2855	0
2856	0
2857	0
2858	0
2859	0
2860	0
2861	0
2862	0
2863	0
2864	0
2865	0
2866	0
2867	0
2868	0
2869	0
2870	0
2871	0
2872	0
2873	0
2874	0
2875	0
2876	0
2877	0
2878	0
2879	0
2880	0
2881	0
2882	0
2883	0
2884	0
2885	0
2886	0
2887	0
2888	0
2889	0
2890	0
2891	0
2892	0
2893	0
2894	0
2895	0
2896	0
2897	0
2898	0
2899	0
2900	0
2901	1
2902	0
2903	1
2904	0
2905	0
2906	0
2907	0
2908	1
2909	1
2910	0
2911	0
2912	0
2913	0
2914	0
2915	0
2916	1
2917	1
2918	0
2919	0
2920	1
2921	1
2922	0
2923	0
2924	0
2925	0
2926	0
2927	0
2928	1
2929	1
2930	0
2931	0
2932	0
2933	0
2934	0
2935	0
2936	1
2937	1
2938	0
2939	0
2940	0
2941	0
2942	0
2943	0
2944	0
2945	0
2946	0
2947	0
2948	0
2949	0
2950	0
2951	0
2952	0
2953	0
2954	0
2955	0
2956	0
2957	0
2958	0
2959	0
2960	0
2961	0
2962	0
2963	0
2964	0
2965	0
2966	0
2967	0
2968	0
2969	0
2970	0
2971	0
2972	0
2973	0
2974	0
2975	0
2976	0
2977	0
2978	0
2979	0
2980	0
2981	0
2982	0
2983	0
2984	0
2985	0
2986	0
2987	0
2988	0
2989	0
2990	0
2991	0
2992	0
2993	0
2994	0
2995	0
2996	0
2997	0
2998	0
2999	0
3000	0
3001	0
3002	0
3003	0
3004	0
3005	0
3006	0
3007	0
3008	0
3009	0
3010	0
3011	0
3012	0
3013	0
3014	0
3015	0
3016	0
3017	0
3018	0
3019	0
3020	0
3021	0
3022	0
3023	0
3024	0
3025	0
3026	0
3027	0
3028	0
3029	0
3030	0
3031	0
3032	0
3033	0
3034	0
3035	0
3036	0
3037	0
3038	0
3039	0
3040	0
3041	0
3042	0
3043	0
3044	0
3045	0
3046	0
3047	0
3048	0
3049	0
3050	0
3051	0
3052	0
3053	0
3054	0
3055	0
3056	0
3057	0
3058	0
3059	0
3060	0
3061	0
3062	0
3063	0
3064	0
3065	0
3066	0
3067	0
3068	0
3069	0
3070	0
3071	0
3072	0
3073	0
3074	0
3075	0
3076	0
3077	0
3078	0
3079	0
3080	0
3081	1
3082	0
3083	0
3084	0
3085	0
3086	0
3087	0
3088	0
3089	1
3090	1
3091	0
3092	0
3093	0
3094	0
3095	0
3096	1
3097	1
3098	0
3099	0
3100	1
3101	0
3102	0
3103	0
3104	0
3105	0
3106	0
3107	0
3108	1
3109	0
3110	0
3111	0
3112	0
3113	0
3114	1
3115	0
3116	0
3117	0
3118	0
3119	0
3120	1
3121	0
3122	0
3123	0
3124	0
3125	0
3126	0
3127	0
3128	0
3129	0
3130	0
3131	0
3132	0
3133	0
3134	0
3135	0
3136	0
3137	0
3138	0
3139	0
3140	0
3141	0
3142	0
3143	0
3144	0
3145	0
3146	0
3147	0
3148	0
3149	0
3150	0
3151	0
3152	0
3153	0
3154	0
3155	0
3156	1
3157	0
3158	0
3159	0
3160	0
3161	0
3162	0
3163	0
3164	0
3165	0
3166	0
3167	0
3168	0
3169	0
3170	0
3171	0
3172	0
3173	0
3174	0
3175	0
3176	0
3177	0
3178	0
3179	0
3180	0
3181	0
3182	0
3183	0
3184	0
3185	0
3186	0
3187	0
3188	0
3189	0
3190	0
3191	0
3192	0
3193	0
3194	0
3195	0
3196	0
3197	0
3198	0
3199	0
3200	0
3201	0
3202	0
3203	0
3204	0
3205	0
3206	0
3207	0
3208	0
3209	0
3210	0
3211	0
3212	0
3213	0
3214	0
3215	0
3216	0
3217	0
3218	0
3219	0
3220	0
3221	0
3222	0
3223	0
3224	0
3225	0
3226	0
3227	0
3228	0
3229	0
3230	0
3231	0
3232	0
3233	0
3234	0
3235	0
3236	0
3237	0
3238	0
3239	0
3240	0
3241	1
3242	0
3243	1
3244	0
3245	0
3246	0
3247	0
3248	1
3249	0
3250	0
3251	0
3252	0
3253	0
3254	0
3255	0
3256	1
3257	1
3258	0
3259	0
3260	1
3261	0
3262	0
3263	0
3264	0
3265	0
3266	0
3267	0
3268	0
3269	0
3270	1
3271	0
3272	0
3273	0
3274	1
3275	0
3276	1
3277	0
3278	0
3279	0
3280	1
3281	0
3282	0
3283	0
3284	0
3285	0
3286	0
3287	0
3288	0
3289	0
3290	0
3291	0
3292	0
3293	0
3294	0
3295	0
3296	0
3297	0
3298	0
3299	0
3300	0
3301	0
3302	0
3303	0
3304	0
3305	0
3306	0
3307	0
3308	0
3309	0
3310	0
3311	0
3312	0
3313	0
3314	0
3315	0
3316	0
3317	0
3318	0
3319	0
3320	0
3321	0
3322	0
3323	0
3324	0
3325	0
3326	0
3327	0
3328	0
3329	1
3330	0
3331	0
3332	0
3333	0
3334	0
3335	0
3336	0
3337	1
3338	0
3339	0
3340	0
3341	0
3342	0
3343	0
3344	0
3345	0
3346	0
3347	0
3348	0
3349	0
3350	0
3351	0
3352	0
3353	0
3354	0
3355	0
3356	0
3357	0
3358	0
3359	0
3360	0
3361	0
3362	0
3363	0
3364	0
3365	0
3366	0
3367	0
3368	0
3369	0
3370	0
3371	0
3372	0
3373	0
3374	0
3375	0
3376	0
3377	0
3378	0
3379	0
3380	0
3381	0
3382	0
3383	0
3384	0
3385	0
3386	0
3387	0
3388	0
3389	0
3390	1
3391	0
3392	0
3393	0
3394	1
3395	0
3396	0
3397	0
3398	0
3399	0
3400	0
3401	0
3402	0
3403	0
3404	0
3405	0
3406	0
3407	0
3408	1
3409	1
3410	0
3411	0
3412	0
3413	0
3414	0
3415	0
3416	0
3417	0
3418	0
3419	0
3420	0
3421	0
3422	0
3423	0
3424	0
3425	0
3426	0
3427	0
3428	0
3429	0
3430	0
3431	0
3432	0
3433	0
3434	0
3435	0
3436	0
3437	0
3438	0
3439	0
3440	0
3441	0
3442	0
3443	0
3444	0
3445	0
3446	0
3447	0
3448	0
3449	0
3450	0
3451	0
3452	0
3453	0
3454	0
3455	0
3456	0
3457	0
3458	0
3459	0
3460	0
3461	0
3462	0
3463	0
3464	0
3465	0
3466	0
3467	0
3468	0
3469	0
3470	0
3471	0
3472	0
3473	0
3474	0
3475	0
3476	0
3477	0
3478	0
3479	0
3480	0
3481	0
3482	0
3483	0
3484	0
3485	0
3486	0
3487	0
3488	0
3489	0
3490	0
3491	0
3492	0
3493	0
3494	0
3495	0
3496	0
3497	0
3498	0
3499	0
3500	0
3501	0
3502	0
3503	0
3504	0
3505	0
3506	0
3507	0
3508	0
3509	0
3510	0
3511	0
3512	0
3513	0
3514	0
3515	0
3516	0
3517	0
3518	0
3519	0
3520	0
3521	0
3522	0
3523	0
3524	0
3525	0
3526	0
3527	0
3528	0
3529	0
3530	0
3531	0
3532	0
3533	0
3534	0
3535	0
3536	0
3537	0
3538	0
3539	0
3540	0
3541	0
3542	0
3543	0
3544	0
3545	0
3546	0
3547	0
3548	0
3549	0
3550	0
3551	0
3552	0
3553	0
3554	0
3555	0
3556	0
3557	0
3558	0
3559	0
3560	0
3561	0
3562	0
3563	1
3564	0
3565	0
3566	0
3567	0
3568	1
3569	0
3570	0
3571	0
3572	0
3573	0
3574	0
3575	0
3576	0
3577	0
3578	0
3579	0
3580	0
3581	0
3582	0
3583	1
3584	0
3585	0
3586	0
3587	0
3588	1
3589	1
3590	0
3591	0
3592	0
3593	0
3594	0
3595	0
3596	0
3597	0
3598	0
3599	0
3600	1
3601	0
3602	0
3603	0
3604	0
3605	0
3606	0
3607	0
3608	0
3609	0
3610	1
3611	0
3612	0
3613	0
3614	0
3615	0
3616	0
3617	0
3618	0
3619	0
3620	0
3621	0
3622	0
3623	0
3624	0
3625	0
3626	0
3627	0
3628	0
3629	0
3630	0
3631	0
3632	0
3633	0
3634	0
3635	0
3636	0
3637	0
3638	0
3639	0
3640	0
3641	0
3642	0
3643	0
3644	0
3645	0
3646	0
3647	0
3648	0
3649	0
3650	0
3651	0
3652	0
3653	0
3654	0
3655	0
3656	0
3657	0
3658	0
3659	0
3660	0
3661	0
3662	0
3663	0
3664	0
3665	0
3666	0
3667	0
3668	1
3669	1
3670	0
3671	0
3672	0
3673	0
3674	0
3675	0
3676	0
3677	0
3678	0
3679	0
3680	1
3681	0
3682	0
3683	0
3684	0
3685	0
3686	0
3687	0
3688	0
3689	0
3690	0
3691	0
3692	0
3693	0
3694	0
3695	0
3696	0
3697	0
3698	0
3699	0
3700	0
3701	0
3702	0
3703	0
3704	0
3705	0
3706	0
3707	0
3708	0
3709	0
3710	0
3711	0
3712	0
3713	0
3714	0
3715	0
3716	0
3717	0
3718	0
3719	0
3720	0
3721	1
3722	0
3723	0
3724	0
3725	0
3726	0
3727	0
3728	1
3729	0
3730	0
3731	0
3732	0
3733	0
3734	0
3735	0
3736	1
3737	0
3738	0
3739	0
3740	0
3741	1
3742	0
3743	1
3744	0
3745	0
3746	0
3747	0
3748	0
3749	0
3750	1
3751	0
3752	0
3753	0
3754	0
3755	0
3756	0
3757	0
3758	0
3759	0
3760	1
3761	0
3762	0
3763	0
3764	0
3765	0
3766	0
3767	0
3768	0
3769	0
3770	0
3771	0
3772	0
3773	0
3774	0
3775	0
3776	0
3777	0
3778	0
3779	0
3780	0
3781	0
3782	0
3783	0
3784	0
3785	0
3786	0
3787	0
3788	0
3789	0
3790	0
3791	0
3792	0
3793	0
3794	0
3795	0
3796	0
3797	0
3798	0
3799	0
3800	0
3801	0
3802	0
3803	0
3804	0
3805	0
3806	0
3807	0
3808	0
3809	0
3810	0
3811	0
3812	0
3813	0
3814	0
3815	0
3816	0
3817	0
3818	0
3819	0
3820	0
3821	0
3822	0
3823	0
3824	0
3825	0
3826	0
3827	0
3828	0
3829	0
3830	0
3831	0
3832	0
3833	0
3834	0
3835	0
3836	0
3837	0
3838	0
3839	0
3840	0
3841	1
3842	0
3843	1
3844	0
3845	0
3846	0
3847	0
3848	1
3849	0
3850	0
3851	0
3852	0
3853	0
3854	0
3855	0
3856	0
3857	1
3858	0
3859	0
3860	0
3861	0
3862	0
3863	0
3864	0
3865	0
3866	0
3867	0
3868	0
3869	0
3870	0
3871	0
3872	0
3873	0
3874	0
3875	0
3876	0
3877	0
3878	0
3879	0
3880	0
3881	0
3882	0
3883	0
3884	0
3885	0
3886	0
3887	0
3888	0
3889	0
3890	0
3891	0
3892	0
3893	0
3894	0
3895	0
3896	0
3897	0
3898	0
3899	0
3900	0
3901	0
3902	0
3903	0
3904	0
3905	0
3906	0
3907	0
3908	0
3909	0
3910	0
3911	0
3912	0
3913	0
3914	0
3915	0
3916	0
3917	0
3918	0
3919	0
3920	0
3921	0
3922	0
3923	0
3924	0
3925	0
3926	0
3927	0
3928	0
3929	0
3930	0
3931	0
3932	0
3933	0
3934	0
3935	0
3936	0
3937	0
3938	0
3939	0
3940	0
3941	0
3942	0
3943	0
3944	0
3945	0
3946	0
3947	0
3948	0
3949	0
3950	0
3951	0
3952	0
3953	0
3954	0
3955	0
3956	0
3957	0
3958	0
3959	0
3960	0
3961	0
3962	0
3963	0
3964	0
3965	0
3966	0
3967	0
3968	0
3969	0
3970	0
3971	0
3972	0
3973	0
3974	0
3975	0
3976	0
3977	0
3978	0
3979	0
3980	0
3981	0
3982	0
3983	0
3984	0
3985	0
3986	0
3987	0
3988	0
3989	0
3990	0
3991	0
3992	0
3993	0
3994	0
3995	0
3996	0
3997	0
3998	0
3999	0
4000	0
4001	0
4002	0
4003	0
4004	0
4005	0
4006	0
4007	0
4008	0
4009	0
4010	0
4011	0
4012	0
4013	0
4014	0
4015	0
4016	0
4017	0
4018	0
4019	0
4020	0
4021	0
4022	0
4023	0
4024	0
4025	0
4026	0
4027	0
4028	0
4029	0
4030	0
4031	0
4032	0
4033	0
4034	0
4035	0
4036	0
4037	0
4038	0
4039	0
4040	0
4041	0
4042	0
4043	1
4044	0
4045	0
4046	0
4047	0
4048	0
4049	0
4050	1
4051	0
4052	0
4053	0
4054	1
4055	0
4056	0
4057	1
4058	0
4059	0
4060	0
4061	0
4062	0
4063	0
4064	0
4065	0
4066	0
4067	0
4068	1
4069	0
4070	1
4071	0
4072	0
4073	0
4074	0
4075	0
4076	0
4077	1
4078	0
4079	0
4080	1
4081	0
4082	0
4083	0
4084	0
4085	0
4086	0
4087	0
4088	0
4089	0
4090	0
4091	0
4092	0
4093	0
4094	0
4095	0
4096	0
4097	0
4098	0
4099	0
4100	0
4101	0
4102	0
4103	0
4104	0
4105	0
4106	0
4107	0
4108	0
4109	0
4110	0
4111	0
4112	0
4113	0
4114	0
4115	0
4116	0
4117	0
4118	0
4119	0
4120	0
75242	1
75243	0
75244	1
75245	0
75246	0
75247	0
75248	0
75249	0
75250	0
75251	0
75252	1
75253	0
75254	0
75255	0
75256	0
75257	0
75258	0
75259	0
75260	0
75261	0
75262	0
75263	0
75264	0
75265	0
75266	0
75267	0
75268	0
75269	0
75270	0
75271	0
75272	1
75273	0
75274	0
75275	1
75276	1
75277	0
75278	0
75279	0
75280	1
75281	0
75282	0
75283	0
75284	0
75285	0
75286	0
75287	0
75288	0
75289	0
75290	0
75291	0
75292	0
75293	0
75294	0
75295	0
75296	1
75297	0
75298	0
75299	0
75300	0
75301	0
75302	0
75303	1
75304	0
75305	0
75306	0
75307	1
75308	0
75309	0
75310	0
75311	0
75312	0
75313	0
75314	0
75315	0
75316	0
75317	0
75318	0
75319	1
75320	0
75321	0
75322	0
75323	1
75324	0
75325	0
75326	0
75327	0
75328	0
75329	0
75330	0
75331	1
75332	0
75333	0
75334	0
75335	0
75336	0
75337	0
75338	0
75339	0
75340	0
75341	0
75342	0
75343	0
75344	0
75345	0
75346	0
75347	0
75348	0
75349	0
75350	0
75351	1
75352	0
75353	0
75354	0
75355	1
75356	0
75357	0
75358	0
75359	1
75360	0
75361	0
75362	0
75363	0
75364	0
75365	0
75366	0
75367	0
75368	0
75369	0
75370	0
75371	0
75372	0
75373	0
75374	0
75375	1
75376	0
75377	0
75378	0
75379	0
75380	0
75381	0
75382	0
75383	1
75384	0
75385	0
75386	0
75387	1
75388	0
75389	0
75390	0
75391	0
75392	0
75393	0
75394	0
75395	0
75396	0
75397	0
75398	0
75399	1
75400	0
75401	0
75402	0
75403	1
75404	0
75405	0
75406	0
75407	0
75408	0
75409	0
75410	0
75411	1
75412	0
75413	0
75414	0
75415	0
75416	0
75417	0
75418	0
75419	0
75420	0
75421	0
75422	0
75423	0
75424	0
75425	0
75426	0
75427	0
75428	0
75429	0
75430	0
75431	1
75432	0
75433	0
75434	0
75435	1
75436	0
75437	0
75438	0
75439	1
75440	0
75441	0
75442	0
75443	0
75444	0
75445	0
75446	0
75447	0
75448	0
75449	0
75450	0
75451	0
75452	0
75453	0
75454	0
75455	1
75456	0
75457	0
75458	0
75459	0
75460	0
75461	0
75462	0
75463	1
75464	0
75465	0
75466	0
75467	1
75468	0
75469	0
75470	0
75471	0
75472	0
75473	0
75474	0
75475	0
75476	0
75477	0
75478	0
75479	1
75480	0
75481	0
""")
    resource20("reference/paper_zero/joint_two_witness_STAGE2_END_STATE.csv","3c66893748c4b19be962a1b8e4fc5bcbec26797db02b2833ffdfbb990112ce4a","""road,z,Cc_kW,Ce_kWh,Cv_kW
\"1\",\"1.0\",\"400.0\",\"40.0\",\"60.0\"
\"2\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"3\",\"1.0\",\"300.0\",\"40.0\",\"60.0\"
\"4\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"5\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"6\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"7\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"8\",\"1.0\",\"200.0\",\"40.0\",\"60.0\"
\"9\",\"1.0\",\"400.0\",\"40.0\",\"60.0\"
\"10\",\"1.0\",\"200.0\",\"40.0\",\"60.0\"
\"11\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"12\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"13\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"14\",\"1.0\",\"200.0\",\"40.0\",\"60.0\"
\"15\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"16\",\"1.0\",\"200.0\",\"40.0\",\"60.0\"
\"17\",\"1.0\",\"200.0\",\"40.0\",\"60.0\"
\"18\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"19\",\"0.0\",\"0.0\",\"0.0\",\"0.0\"
\"20\",\"1.0\",\"200.0\",\"40.0\",\"60.0\"
""")
    resource20("reference/paper_zero/nominal_SUMMARY.csv","d1f34d66c05323e6f0614b54542f3d4ee14e18103db7762da0a6329f0aaa5297","""branch,scenario,status,termination,primal,lower_bound,upper_incumbent,independent_stage3_cost,has_incumbent,is_optimal,audit_ok,variables,binaries,constraints,max_model_violation,max_independent_residual,state_grid_ok,objective_rebuild_residual,stage2_predecessor_sha256,source_sha256,build_seconds,solve_wall_seconds,solver_reported_seconds,configured_time_limit,highs_time_limit_readback,moi_time_limit_readback,time_limit_readback_ok,time_overrun_flag,full_phi3_oracle_certified
\"paper_zero\",\"nominal\",\"OPTIMAL_AUDITED\",\"OPTIMAL\",\"FEASIBLE_POINT\",\"1.008405179408447e6\",\"1.008405179408447e6\",\"1.0084051794084457e6\",\"true\",\"true\",\"true\",\"75481\",\"4180\",\"153238\",\"0.0\",\"1.3783574104309082e-7\",\"true\",\"1.280568540096283e-9\",\"3c66893748c4b19be962a1b8e4fc5bcbec26797db02b2833ffdfbb990112ce4a\",\"70f976f717ab3674ea7142717f62dc6b6c125bc3da4ec04f321c968efd1eb8f5\",\"14.403000116348267\",\"226.87800002098083\",\"225.87494611740112\",\"1800.0\",\"1800.0\",\"1800.0\",\"true\",\"false\",\"false\"
""")
    resource20("reference/paper_zero/stress_SUMMARY.csv","10ab913a09bb4333d2d88e55ea0b2f3e2a2dc93de68aaaf2c4a3e8c390aa04ac","""branch,scenario,status,termination,primal,lower_bound,upper_incumbent,independent_stage3_cost,has_incumbent,is_optimal,audit_ok,variables,binaries,constraints,max_model_violation,max_independent_residual,state_grid_ok,objective_rebuild_residual,stage2_predecessor_sha256,source_sha256,build_seconds,solve_wall_seconds,solver_reported_seconds,configured_time_limit,highs_time_limit_readback,moi_time_limit_readback,time_limit_readback_ok,time_overrun_flag,full_phi3_oracle_certified
\"paper_zero\",\"stress\",\"OPTIMAL_AUDITED\",\"OPTIMAL\",\"FEASIBLE_POINT\",\"1.6826647747362368e6\",\"1.6826647747362368e6\",\"1.6826647747362298e6\",\"true\",\"true\",\"true\",\"75481\",\"4180\",\"153238\",\"0.0\",\"1.4528632164001465e-7\",\"true\",\"6.984919309616089e-9\",\"3c66893748c4b19be962a1b8e4fc5bcbec26797db02b2833ffdfbb990112ce4a\",\"70f976f717ab3674ea7142717f62dc6b6c125bc3da4ec04f321c968efd1eb8f5\",\"14.871999979019165\",\"443.9859998226166\",\"442.9611761569977\",\"1800.0\",\"1800.0\",\"1800.0\",\"true\",\"false\",\"false\"
""")
end
load_resources20()
include(joinpath(RUNTIME20,"driver.jl"))

# ادامهٔ حل ترمینال دورهٔ سوم، برای حالت دورهٔ دوم در اجرای ارسالی
const Core20 = REVCSCertifiedCore

function event20(o, step, detail)
    open(joinpath(o.output,"PROGRESS.tsv"),"a") do io
        println(io, step, '\t', detail)
    end
    println(step, "  ", detail)
    flush(stdout)
end

function read_pattern20(path, vars)
    lines = readlines(path)
    first(lines) == "variable_index\tvalue" || error("Invalid column header")
    length(lines) == length(vars)+1 || error("Incomplete integer column")
    vals = Int[]
    for (v,line) in zip(vars, Iterators.drop(lines,1))
        i,k = parse.(Int,split(line,'\t'))
        i == index(v).value || error("Column layout differs from the stage model")
        is_binary(v) && !(k in (0,1)) && error("Invalid binary decision")
        push!(vals,k)
    end
    return Core20.IntegerPattern([index(v).value for v in vars], vals)
end

# برگرداندن دقیق سناریوی استخراج‌شده، شامل علامت صفر و تمام مؤلفه‌های مشتق‌شده
function witness20(path)
    u,_=g742_fix13_realization("nominal")
    u["name"]="FIX19 archived production witness"
    open(path) do io
        readline(io)=="component\tindex\tvalue" || error("Invalid witness header")
        for k in sort(collect(keys(u)))
            k=="name" && continue
            x=u[k]
            for i in (x isa Number ? (nothing,) : CartesianIndices(x))
                label,idx,val=split(readline(io),'\t')
                label==k && idx==(i===nothing ? "scalar" : join(Tuple(i),',')) ||
                    error("Invalid archived witness layout")
                v=parse(Float64,val)
                isfinite(v) || error("Nonfinite witness component")
                if i===nothing
                    u[k]=v
                else
                    x[i]=v
                end
            end
        end
        eof(io) || error("Trailing witness rows")
    end
    validate_scenario(3,u)
    return u
end

function pool20(o, builder, domain, state_sha, scope)
    folder = joinpath(G742_ROOT,"checkpoint")
    info = g742_csvone(joinpath(folder,"FIX17_NATIVE_PRODUCTION.csv"))
    (info["branch"],info["stage"],info["scope"],info["predecessor_sha256"]) ==
        (o.branch,"3",scope,state_sha) || error("Checkpoint belongs to another problem")
    witness = witness20(joinpath(folder,"FIX17_EXTRACTED_SCENARIO.tsv"))
    digest(u) = bytes2hex(sha256(g742_fix15_numeric_bytes(u)))
    digest(witness) == info["extracted_scenario_sha256"] || error("Archived witness mismatch")
    seed = first(domain.factory())
    digest(seed) == info["seed_scenario_sha256"] || error("Archived initial scenario mismatch")
    model = builder(seed)
    vars = filter(v->is_binary(v)||is_integer(v), all_variables(model))
    columns = [read_pattern20(joinpath(folder,file),vars) for file in
        ("FIX17_COLUMN_PATTERN.tsv","FIX17_NEXT_INNER_INTEGER_PATTERN.tsv")]
    count(columns[1].values .!= columns[2].values) == parse(Int,info["next_inner_hamming_from_farkas_column"]) ||
        error("Archived column distance mismatch")
    lower = parse(Float64,info["next_inner_lower_bound"])
    info["next_inner_feasible"]=="true" && info["initial_inner_feasible"]=="true" &&
        isfinite(lower) && lower <= parse(Float64,info["next_inner_incumbent"]) || error("Invalid archived replay")
    if FIX20_RESUME[] !== nothing
        # فایل نمایه بعد از اتمام نوشتن ستون منتشر می‌شود. ستون نیمه‌نوشته وارد مستر نمی‌شود.
        dir = FIX20_RESUME[]
        manifest = readlines(joinpath(dir,"POOL.tsv"))
        first(manifest) == join((MODEL_SOURCE_HASH,state_sha,scope),'\t') || error("Resume scope mismatch")
        for (i,line) in enumerate(manifest[2:end])
            filename,h = split(line,'\t')
            filename == "column_$i.tsv" || error("Invalid resume filename")
            p = joinpath(dir,filename)
            bytes2hex(sha256(read(p))) == h || error("Damaged resume column")
            col = read_pattern20(p,vars)
            if i <= 2
                col.values == columns[i].values || error("Resume seed differs")
            else
                any(c->c.values==col.values,columns) && error("Duplicate resume column")
                push!(columns,col)
            end
        end
        length(manifest) >= 3 || error("Incomplete resume pool")
    end
    event20(o,"CHECKPOINT_VALIDATED","columns=$(length(columns))  integer_variables=$(length(vars))  stage=3")
    return columns,witness,lower
end

function save_pool20(o, columns, state_sha, scope)
    dir = o.output
    open(joinpath(dir,"POOL.tsv.tmp"),"w") do io
        println(io, join((MODEL_SOURCE_HASH,state_sha,scope),'\t'))
        for (i,p) in enumerate(columns)
            name = "column_$i.tsv"
            file = joinpath(dir,name)
            if !isfile(file)
                g742_fix17_write_pattern(file*".tmp",p)
                mv(file*".tmp",file)
            end
            println(io,name,'\t',bytes2hex(sha256(read(file))))
        end
    end
    Base.Filesystem.rename(joinpath(dir,"POOL.tsv.tmp"),joinpath(dir,"POOL.tsv"))
end

# انتخاب سناریو با استفاده از همان متغیرهای دودویی و پروفیل‌های فیزیکی مدل
function candidates20()
    hi,_ = g742_fix13_realization("all-plus")
    lo,_ = g742_fix13_realization("all-minus")
    nominal,_ = g742_fix13_realization("nominal")
    mixed = create_uncertainty_scenario("high demand, low renewable",3,
        hi["omega_u_plus"],hi["omega_u_minus"],lo["omega_p_plus"],lo["omega_p_minus"],
        lo["beta_wt_plus"],lo["beta_wt_minus"],lo["beta_pv_plus"],lo["beta_pv_minus"],
        lo["psi_plus"],lo["psi_minus"])
    validate_scenario(3,mixed)
    return [mixed, lo, nominal, hi]
end

# تک‌سناریو فقط هنگامی شاهد جداسازی است که LP هر ستون در همان سناریو ناممکن باشد.
function excluded20(builder,u,p,seconds)
    lp = builder(u)
    Core20.fix_pattern!(lp,p)
    @objective(lp,Min,0)
    set_time_limit_sec(lp,seconds)
    Core20.solve_tracked!(lp;context="fixed_column_feasibility_lp")
    return termination_status(lp)
end

function screen20(o,builder,columns,candidates,known_covered)
    for (j,u) in enumerate(candidates)
        j in known_covered && continue
        separated = true
        for (i,p) in enumerate(columns)
            status = excluded20(builder,u,p,o.seconds)
            event20(o,"SCREEN_LP","scenario=$(u["name"])  column=$i  status=$status")
            if status != MOI.INFEASIBLE
                status==MOI.OPTIMAL && push!(known_covered,j)
                separated = false
                break
            end
        end
        separated && return u
    end
    return nothing
end

function separate20(o,columns,fac,block)
    a = Core20.farkas_audit_symbolic_master(columns,fac,block,HiGHS.Optimizer;
        seconds=o.seconds,threads=o.threads,sign_aware=true)
    m = a.model
    a.metrics["column_link_rows"]==length(columns) && a.metrics["variable_count_delta"]==0 &&
        a.metrics["constraint_count_delta"]==0 && get(a.metrics,"indicator_constraints",0)==0 ||
        error("Invalid multi-column Farkas construction")
    # در HiGHS 1.16 این حذف می‌تواند در پیش‌حل مستر بزرگ از مهلت عبور کند.
    # فقط قاعدهٔ مزبور غیرفعال می‌شود. قیود و سایر قواعد پیش‌حل همان مدل باقی می‌مانند.
    if isdefined(HiGHS,:kHighsPresolveRuleFourierMotzkin)
        mask=1 << HiGHS.kHighsPresolveRuleFourierMotzkin
        set_optimizer_attribute(m,"presolve_rule_off",mask)
        event20(o,"FARKAS_PRESOLVE","disabled=FourierMotzkin  mask=$mask")
    end
    event20(o,"FARKAS_MODEL","columns=$(length(columns))  variables=$(num_variables(m))")
    Core20.solve_tracked!(m;context="multi_column_sign_aware_farkas")
    audit = Core20.farkas_audit_mip_incumbent(m;tol=1e-6)
    write_rows(joinpath(o.output,"FARKAS_LAST_AUDIT.csv"),[audit])
    st=termination_status(m)
    st==MOI.INFEASIBLE && error("Infeasible normalized Farkas master")
    ub=try objective_bound(m) catch; Inf end
    gate=Core20.farkas_gate(st,audit.independent_incumbent_validated,audit.incumbent_objective,ub)
    event20(o,"FARKAS_RESULT","status=$st  gate=$gate  bound=$ub")
    u=gate==:witness ? a.extract() : nothing
    u!==nothing && validate_scenario(3,u)
    return gate,u
end

function inner20(o,builder,u; feasibility)
    validate_scenario(3,u)
    m=builder(u)
    # در فاز امکان‌پذیری فقط الگوی جدید لازم است. تابع صفر هیچ کران هزینه‌ای تولید نمی‌کند.
    feasibility && @objective(m,Min,0)
    Core20.solve_tracked!(m;context=feasibility ? "inner_find_feasible_column" : "inner_physical_cost")
    row=Core20.min_bounds(m)
    event20(o,"INNER_RESULT","feasibility_only=$feasibility  status=$(row.status)  feasible=$(row.feasible)")
    return row, row.feasible ? Core20.integer_pattern(m) : nothing
end

# قیمت‌گذاری آغازین در یک سناریوی معتبر. هزینهٔ جواب آزاد فقط با کران‌های همان سناریو مقایسه می‌شود.
function price20(o,builder,u,columns)
    pool_lower=Inf
    best_cost=Inf
    start=nothing
    for (i,col) in enumerate(columns)
        lp=builder(u)
        Core20.fix_pattern!(lp,col)
        Core20.solve_tracked!(lp;context="price_fixed_column")
        row=Core20.min_bounds(lp)
        pool_lower=min(pool_lower,row.lower)
        if row.feasible && row.upper<best_cost
            best_cost=row.upper
            start=value.(all_variables(lp))
        end
        event20(o,"PRICE_FIXED","column=$i  status=$(row.status)  lower=$(row.lower)  upper=$(row.upper)")
    end
    m=builder(u)
    if start!==nothing
        vars=all_variables(m)
        length(vars)==length(start) || error("Warm start layout mismatch")
        set_start_value.(vars,start)
    end
    Core20.solve_tracked!(m;context="price_unrestricted_physical_cost")
    row=Core20.min_bounds(m)
    improved=row.feasible && isfinite(pool_lower) && row.upper < pool_lower-o.tol*max(1.0,abs(pool_lower))
    event20(o,"PRICE_RESULT","status=$(row.status)  pool_lb=$pool_lower  incumbent=$(row.upper)  lower=$(row.lower)  improved=$improved")
    improved || return row,nothing
    p=Core20.integer_pattern(m)
    verify=builder(u)
    Core20.fix_pattern!(verify,p)
    Core20.solve_tracked!(verify;context="verify_priced_column_lp")
    verified=Core20.min_bounds(verify)
    accepted=verified.feasible && verified.upper < pool_lower-o.tol*max(1.0,abs(pool_lower))
    event20(o,"PRICE_REPLAY","status=$(verified.status)  upper=$(verified.upper)  accepted=$accepted")
    return row, accepted ? p : nothing
end

function optimality20(o,columns,fac,block)
    m,extract=Core20.symbolic_master(columns,fac,block,g7_scip_optimizer();seconds=o.seconds)
    Core20.solve_tracked!(m;context="optimality_indicator_master")
    status=termination_status(m)
    status in (MOI.INFEASIBLE,MOI.INFEASIBLE_OR_UNBOUNDED,MOI.DUAL_INFEASIBLE) &&
        return status,Inf,nothing
    ub=try objective_bound(m) catch; Inf end
    feasible=has_values(m) && primal_status(m)==MOI.FEASIBLE_POINT
    return status,(isnan(ub) ? Inf : ub),feasible ? extract() : nothing
end

function fix20_continue(o,cfg,grids,st,z0,state_sha,scope,domain)
    builder=u->first(build_certified_stage(3,st,u,grids;direction=:lower,seconds=o.seconds,
        capacity_mode=cfg.capacity_mode,initial_station_state=z0))
    block=(m,u)->build_certified_stage(3,st,u,grids;direction=:lower,seconds=o.seconds,
        capacity_mode=cfg.capacity_mode,initial_station_state=z0,shared_model=m)
    fac=m->symbolic_uncertainty(m,3)
    columns,best,lower=pool20(o,builder,domain,state_sha,scope)
    save_pool20(o,columns,state_sha,scope)
    history=NamedTuple[]
    upper=Inf
    result(reason;converged=false,infeasible=false) = Core20.CCGResult(lower,upper,converged,
        infeasible,best,columns,history,scope,reason,:exact)
    candidates=candidates20()
    known_covered=Set{Int}()
    for iteration in 1:o.iters
        event20(o,"ITERATION","index=$iteration  columns=$(length(columns))")
        if iteration==1 && length(columns)==2
            probe=first(candidates)
            row,p=price20(o,builder,probe,columns)
            if row.status==MOI.INFEASIBLE
                lower=Inf;upper=Inf;best=probe
                push!(history,(;iteration,phase=:pricing,lower,upper,columns=length(columns),master_complete=false))
                return result(:robust_infeasible;infeasible=true)
            end
            if row.lower>lower
                lower=row.lower;best=probe
            end
            if p!==nothing
                any(c->c.values==p.values,columns) && error("Duplicate column contradicts pricing bounds")
                push!(columns,p)
                save_pool20(o,columns,state_sha,scope)
                g742_fix17_write_scenario_snapshot(joinpath(o.output,"pricing_scenario.tsv"),probe)
                event20(o,"COLUMN_SAVED","iteration=$iteration  columns=$(length(columns))  source=pricing")
                push!(history,(;iteration,phase=:pricing,lower,upper,columns=length(columns),master_complete=false))
                continue
            end
        end
        u=screen20(o,builder,columns,candidates,known_covered)
        # نبود شاهد بین این چند سناریو مستلزم حل مستر کامل است.
        gate=:witness
        if u===nothing
            GC.gc()
            gate,u=separate20(o,columns,fac,block)
        end
        phase=gate==:covered ? :optimality : (gate==:witness ? :feasibility : :feasibility_unresolved)
        complete=false
        record()=push!(history,(;iteration,phase,lower,upper,columns=length(columns),master_complete=complete))
        if gate==:unresolved
            record()
            return result(:feasibility_uncertified)
        end
        if gate==:covered
            GC.gc()
            status,ub,u=optimality20(o,columns,fac,block)
            complete=status==MOI.OPTIMAL
            upper=min(upper,ub)
            lower<=upper+1e-6*max(1.0,abs(lower)) || error("Crossed C&CG bounds")
            if Core20.gap_closed(lower,upper,o.gap)
                record()
                return result(:gap;converged=true)
            end
            if u===nothing
                record()
                return result(:optimality_unresolved)
            end
        end
        g742_fix17_write_scenario_snapshot(joinpath(o.output,"scenario_$iteration.tsv"),u)
        row,p=inner20(o,builder,u;feasibility=gate==:witness)
        if row.status==MOI.INFEASIBLE
            lower=Inf;upper=Inf;best=u
            record()
            return result(:robust_infeasible;infeasible=true)
        end
        if gate==:covered && row.lower>lower
            lower=row.lower;best=u
        end
        if gate==:covered
            lower<=upper+1e-6*max(1.0,abs(lower)) || error("Crossed updated C&CG bounds")
            if Core20.gap_closed(lower,upper,o.gap)
                record()
                return result(:gap;converged=true)
            end
        end
        if p===nothing
            record()
            return result(:inner_no_incumbent)
        end
        if any(c->Core20.pattern_key(c)==Core20.pattern_key(p),columns)
            record()
            return result(:repeated_column_unresolved)
        end
        push!(columns,p)
        save_pool20(o,columns,state_sha,scope)
        event20(o,"COLUMN_SAVED","iteration=$iteration  columns=$(length(columns))")
        record()
    end
    return result(:iteration_limit)
end

# مسیر پیش‌فرض کنار فایل است. هر اجرا دایرکتوری مستقلی دارد تا گزارش کهنه با اجرای جدید مخلوط نشود.
function run(args::AbstractVector{<:AbstractString}=String[])
    argv=String.(args)
    resume=filter(a->startswith(a,"--resume-from="),argv)
    length(resume)<=1 || error("Duplicate --resume-from")
    FIX20_RESUME[]=isempty(resume) ? nothing : abspath(split(only(resume),'=';limit=2)[2])
    filter!(a->!startswith(a,"--resume-from="),argv)
    defaults=["--mode=full-phi3","--threads=$(min(4,Sys.CPU_THREADS))",
              "--output=$(joinpath(@__DIR__,"FIX20_"*Dates.format(now(),"yyyymmdd_HHMMSS_sss")*"_"*string(getpid())))"]
    for arg in defaults
        prefix=first(split(arg,'='))*"="
        any(a->startswith(a,prefix),argv) || push!(argv,arg)
    end
    o=g742_args(argv)
    o.branch=="paper_zero" || error("Checkpoint is scoped to paper_zero")
    o.mode in ("full-phi3","domain","solver-check") || error("Unsupported FIX20 mode")
    # ایجاد انحصاری پوشه از تداخل دو اجرای هم‌زمان و بازنویسی نتایج قبلی جلوگیری می‌کند.
    mkpath(dirname(o.output))
    mkdir(o.output)
    println("FIX20_OUTPUT=",o.output)
    flush(stdout)
    try
        o.mode!="domain" && g7_load_scip_for_plan!()
        return Base.invokelatest(g742_main,argv)
    catch e
        open(joinpath(o.output,"EXCEPTION.txt"),"w") do io
            showerror(io,e,catch_backtrace())
        end
        g742_write_status(o.output,["GATE_7_4_2_STATUS"=>"ERROR_UNRESOLVED","FULL_PHI3_ORACLE_CERTIFIED"=>"NO"])
        rethrow()
    end
end
end # REVCSFix20
if abspath(PROGRAM_FILE)==abspath(@__FILE__)
    exit(REVCSFix20.run(ARGS))
end
