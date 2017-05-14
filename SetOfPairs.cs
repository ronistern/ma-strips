using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class SetOfPairs
    {
       public Predicate prop1 = null;
       public Predicate prop2 = null;
       int code = -1;


        public bool Equals(SetOfPairs p2)
        {
            if (Object.ReferenceEquals(this, p2))
                return true;
            if (null == p2)
                return false;
            if (((this.prop1.Equals(p2.prop1) && this.prop2.Equals(p2.prop2))) || (this.prop2.Equals(p2.prop1) && this.prop1.Equals(p2.prop2)))
                return true;
            return false;
        }

       
        public override bool Equals(object obj)
        {
            if (obj is SetOfPairs)
                return Equals((SetOfPairs)obj);
            return false;
        }
        public override int GetHashCode()
        {
            if (code == -1)
                code = ToString().GetHashCode();
            return code;
        }
    }
}
