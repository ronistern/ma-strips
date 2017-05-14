using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class Block
    {
        public GroundedPredicate observePredicate;
        public List<Action> effect;
        public List<Formula> canGet;
        double grade;
        public Block()
        {
            grade = 0;
            canGet = new List<Formula>();
            effect = new List<Action>();
           // canGet = new CompoundFormula(");
        }
        public Block(GroundedPredicate observePredicate)
        {
            grade = 0;
            canGet = new List<Formula>();
            this.observePredicate = observePredicate;
            //canGet = new CompoundFormula();
            effect = new List<Action>();
        }
        public Block(Block b)
        {
            observePredicate = b.observePredicate;
            effect = b.effect;
            canGet = new List<Formula>();
            canGet.AddRange(b.canGet);
            grade = b.grade;
        }
    }
}
