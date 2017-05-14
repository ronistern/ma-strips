using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class CompoundExpression : Expression
    {
        public List<Expression> SubExpressions { get; private set; }
        public string Type
        {
            get;
            set;
        }
        public CompoundExpression()
        {
            SubExpressions = new List<Expression>();
        }
        public override string ToString()
        {
            string s = "(" + Type;
            foreach (Expression e in SubExpressions)
            {
                s += " " + e.ToString();
            }
            s += ")";
            return s;
        }
    }
}
