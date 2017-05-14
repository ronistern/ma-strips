using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    public class MutuallyExclusiveFacts
    {
        public Predicate firstFact;
        public Predicate secondFact;
        public int code = -1;
        public MutuallyExclusiveFacts(Predicate a, Predicate b)
        {
            firstFact=a;
            secondFact = b;
        }

        public bool Equals(MutuallyExclusiveFacts p2)
        {
            if (Object.ReferenceEquals(this, p2))
                return true;
            if (null == p2)
                return false;
            if (p2.firstFact.Equals(this.firstFact) && p2.secondFact.Equals(this.secondFact))
                return true;
            if (p2.firstFact.Equals(this.secondFact) && p2.secondFact.Equals(this.firstFact))
                return true;
            return false;
        }


        public override bool Equals(object obj)
        {
            if (obj is MutuallyExclusiveFacts)
                return Equals((MutuallyExclusiveFacts)obj);
            return false;
        }
        public override int GetHashCode()
        {
            if (code == -1)
                code = firstFact.GetHashCode() * secondFact.GetHashCode();
            return code;
        }
    }
}
