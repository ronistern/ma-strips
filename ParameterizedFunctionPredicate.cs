using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    public class ParameterizedFunctionPredicate : ParametrizedPredicate
    {
        public ParameterizedFunctionPredicate(string sName)
            : base(sName)
        {
        }

        public void AddNumber(int x)
        {
            Constant c = new Constant("Number", x + "");
            if (Parameters.Count() == 0)
                throw new ArgumentException("First argument of a function cannot be a number");
            AddParameter(c);
        }
        public void AddFunction(FunctionParameter f)
        {
            AddParameter(f);
        }


        public override GroundedPredicate Ground(Dictionary<string, Constant> dBindings)
        {
            GroundedFunctionPredicate gpred = new GroundedFunctionPredicate(Name);
            gpred.Negation = Negation;
            foreach (Argument a in Parameters)
            {
                if (a is Parameter)
                {
                    if (!dBindings.ContainsKey(a.Name))
                        return null;
                    gpred.AddConstant(dBindings[a.Name]);
                }
                else if (a is Constant)
                {
                    gpred.AddConstant((Constant)a);
                }
                else if (a is FunctionParameter)
                {
                    FunctionParameter fp = (FunctionParameter)a;
                    ParameterizedFunctionPredicate pfp = fp.Function;
                    GroundedFunctionPredicate gfp = (GroundedFunctionPredicate)pfp.Ground(dBindings);
                    FunctionConstant fc = new FunctionConstant(gfp);
                    gpred.AddConstant(fc);

                }
            }
            return gpred;
        }

    }
}
