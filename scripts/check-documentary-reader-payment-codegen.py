"""Balanced full-body inspection of the candidate's two paid entry repairs.
Reject missing coverage and direct unguarded calls. This static review is local:
it does not replace complete consumer inventory or same-production proofs.
"""
import re
from pathlib import Path
HEAD=re.compile(r'(?m)^(?:LEAN_EXPORT\s+|static\s+)?(?:lean_object\s*\*|uint8_t|uint16_t|uint32_t|uint64_t|size_t|void)\s*(?P<name>[A-Za-z_][A-Za-z_0-9]*)\([^;{}]*\)\s*\{')
def bodies(text):
 out={}
 for match in HEAD.finditer(text):
  i=match.end()-1;depth=0;state='code';j=i
  while j<len(text):
   c=text[j];next=text[j+1] if j+1<len(text) else ''
   if state=='code':
    if c=='/' and next=='/':state='line';j+=2;continue
    if c=='/' and next=='*':state='block';j+=2;continue
    if c in ['"',"'"]:state=c
    elif c=='{':depth+=1
    elif c=='}':
     depth-=1
     if depth==0:break
   elif state=='line':
    if c=='\n':state='code'
   elif state=='block':
    if c=='*' and next=='/':state='code';j+=2;continue
   else:
    if c=='\\':j+=2;continue
    if c==state:state='code'
   j+=1
  if depth!=0:raise ValueError('Unbalanced complete body:'+match['name'])
  if match['name'] in out:raise ValueError('Duplicate definition:'+match['name'])
  out[match['name']]=text[i:j+1]
 if not out:raise ValueError('No C definitions inspected')
 return out
CALL=re.compile(r'\b([A-Za-z_][A-Za-z_0-9]*)\s*\(')
CLOSURE=re.compile(r'lean_alloc_closure\(\(void\*\)\(([A-Za-z_][A-Za-z_0-9]*)\)')
BANNED=re.compile(r'\b[A-Za-z_0-9]*(?:PortableAssignment_interpret|EndogenousDecomposition_readAlternatingAssignment|EndogenousDecomposition_readFlippedAssignment|EndogenousDecomposition_readTransportedAssignment|TransportCode_eval)(?:___[A-Za-z_0-9]+)?\s*\(')

def inspect_functions(functions):
 stem=next((n.removesuffix('_recipeCode') for n in functions if n.endswith('_ControlMeasuredAssignmentReader_recipeCode')),None)
 if not stem:raise ValueError('Candidate recipeCode not compiled')
 recipe=stem+'_recipeCode';visit=stem+'_visitCode';prior=visit+'___redArg'
 required=[recipe,visit,prior]
 for name in required:
  if name not in functions:raise ValueError('Missing actual entry:'+name)
 for name,body in functions.items():
  if BANNED.search(body):raise ValueError('Native assignment/index replay:'+name)
 guarding={};callbacks={}
 def entry(name,label):
  body=functions[name]
  if re.search(r'\blean_(?:obj_tag|ctor_get|apply_\d+)\s*\(',body) or re.search(r'\b[A-Za-z_0-9]*_Code_bind(?:___[A-Za-z_0-9]+)?\s*\(',body):raise ValueError('Inspection/application before payment:'+name)
  active={n for n in CALL.findall(body) if n in functions}
  if name==visit and active=={prior}:
   if CALL.findall(body).count(prior)!=1:raise ValueError('Guarded query delegate must be invoked exactly once:'+name)
   return {'delegates_once_to_guarded_redArg':prior}
  if active:raise ValueError('Complex/local call before paid entry:'+name+':'+repr(active))
  constructed=re.findall(r'(v_[A-Za-z_0-9]+)\s*=\s*lean_alloc_ctor\(1, 2, 0\)',body)
  if len(constructed)!=1:raise ValueError('Unique paid Code.step missing:'+name)
  code=constructed[0]
  fields=dict((i,v) for i,v in re.findall(r'lean_ctor_set\('+re.escape(code)+r', ([01]), (v_[A-Za-z_0-9]+)\)',body))
  if set(fields)!={'0','1'}:raise ValueError('Paid step label/callback field missing:'+name)
  boxed=re.search(re.escape(fields['0'])+r'\s*=\s*lean_box\((v_[A-Za-z_0-9]+)\)',body)
  if not boxed or not re.search(re.escape(boxed[1])+r'\s*=\s*'+str(label)+r';',body):raise ValueError('Actual paid label changed/missing:'+name)
  closure=re.search(re.escape(fields['1'])+r'\s*=\s*lean_alloc_closure\(\(void\*\)\(([A-Za-z_0-9]+)\), (\d+), (\d+)\)',body)
  if not closure or closure[1] not in functions:raise ValueError('Captured paid callback missing:'+name)
  target,arity,captured=closure[1],int(closure[2]),int(closure[3])
  all_closures=[]
  for var,fn,a,n in re.findall(r'(v_[A-Za-z_0-9]+)\s*=\s*lean_alloc_closure\(\(void\*\)\(([A-Za-z_0-9]+)\), (\d+), (\d+)\)',body):
   actual_slots=re.findall(r'lean_closure_set\('+re.escape(var)+r', (\d+), (v_[A-Za-z_0-9]+)\)',body)
   if fn not in functions or int(a)<=int(n) or sorted(int(i) for i,_ in actual_slots)!=list(range(int(n))):raise ValueError('Incomplete assembled closure captures:'+name+':'+var)
   all_closures.append({'variable':var,'target':fn,'arity':int(a),'captures':actual_slots})
  if not all_closures:raise ValueError('Assembled closures not inventoried:'+name)
  slots=re.findall(r'lean_closure_set\('+re.escape(fields['1'])+r', (\d+), (v_[A-Za-z_0-9]+)\)',body)
  if arity!=captured+1 or sorted(int(i) for i,_ in slots)!=list(range(captured)):raise ValueError('Incomplete received callback captures:'+name)
  callbacks[name]=target
  return {'label':label,'callback':target,'capture_fields':slots,'all_assembled_closures':all_closures,'direct_constructor_inspections':0,'direct_complex_calls':0}
 guarding[recipe]=entry(recipe,86);guarding[prior]=entry(prior,112);guarding[visit]=entry(visit,112)
 # Named original formation entry calls the already guarded recipe exactly
 # once; it is not the recursive descent. Its only active calls are that
 # entry and one Code.bind. Field projection of the received Formed is fixed.
 formed=stem+'_formedCode___redArg'
 if formed not in functions:raise ValueError('Received Formed entry missing')
 formed_body=functions[formed];formed_calls=CALL.findall(formed_body)
 if formed_calls.count(recipe)!=1 or sum('_Code_bind' in n for n in formed_calls)!=1:raise ValueError('Formed entry must consume one guarded recipe and bind')
 if re.search(r'\blean_(?:obj_tag|apply_\d+)\s*\(',formed_body):raise ValueError('Variable inspection/application in Formed entry')
 if {n for n in formed_calls if n in functions}!={recipe}:raise ValueError('Unreviewed candidate call from Formed entry')
 recursive=[n for n,b in functions.items() if recipe in CALL.findall(b) and n!=formed]
 if recursive!=[callbacks[recipe]]:raise ValueError('Recipe descends outside captured paid callback:'+repr(recursive))
 if not re.search(r'\blean_obj_tag\s*\(',functions[callbacks[recipe]]):raise ValueError('Actual recipe not inspected in paid callback')
 visit_cb=functions[callbacks[prior]]
 if len(re.findall(r'\blean_apply_1\s*\(',visit_cb))!=1:raise ValueError('Received prior Reader must be applied once in paid callback')
 # Exact compiled source perimeter: two query factories within recipeCode
 # (visit and flip), plus the query factory of visitedReader. Function bodies
 # inspected completely, not merely recorded or classified by a lambda name.
 inline=[n for n,b in functions.items() if 'recipeCode___lam__' in n and re.search(r'=\s*112;',b)]
 visited=[n for n,b in functions.items() if 'visitedReader___' in n and 'lean_alloc_ctor(1, 2, 0)' in b]
 if len(inline)!=2 or len(visited)!=1:raise ValueError('Inlined query-factory perimeter changed:'+repr(inline+visited))
 for name in inline+visited:guarding[name]=entry(name,112)
 for name in visited:
  target=callbacks[name]
  if len(re.findall(r'\blean_apply_1\s*\(',functions[target]))!=1:raise ValueError('Visited query callback lost or duplicated prior application')
 return {'definitions_balanced':len(functions),'guarded_entries':guarding,'recursive_call_sites':recursive,
   'nonrecursive_initial_formation_entry':formed,'prior_query_callback':callbacks[prior],'prior_queries_in_callback':1,
   'inlined_reader_factories':inline+visited,'scope':'Complete two repaired APIs plus all3 actual inlined query entries, immutable source/C proofs; final consumer recompilation still required.'}

def inspect(path):
 functions=bodies(Path(path).read_text(encoding='utf-8'));review=inspect_functions(functions);mutations=[]
 for name,data in review['guarded_entries'].items():
  if 'label' not in data:continue
  body=functions[name];label=data['label']
  mutations += [(name,'early_reader_application',body+'\nlean_apply_1(v_prior_999_, v_query_999_);'),
    (name,'wrong_step',body.replace('lean_alloc_ctor(1, 2, 0)','lean_alloc_ctor(2, 2, 0)',1)),
    (name,'wrong_label',re.sub(r'=\s*'+str(label)+r';','= 999;',body,count=1)),
    (name,'missing_capture',re.sub(r'lean_closure_set\([^;]+;', '',body,count=1)),
    (name,'missing_callback_field',re.sub(r'lean_ctor_set\([^;]+, 1, [^;]+;', '',body,count=1))]
 wrapper=next(n for n in review['guarded_entries'] if n.endswith('_visitCode'))
 target=wrapper+'___redArg'
 # The received wrapper is a paid step. Also exercise the explicit ABI
 # delegation compatibility branch with a duplicated guarded delegate.
 duplicate='{ v_first_999_ = '+target+'(v_prior_999_, v_query_999_); v_second_999_ = '+target+'(v_prior_999_, v_query_999_); return v_second_999_; }'
 mutations.append((wrapper,'duplicate_query_delegate',duplicate))
 recipe_name=next(n for n,d in review['guarded_entries'].items() if d.get('label')==86)
 mutations.append((recipe_name,'early_recipe_descent',functions[recipe_name]+'\n'+recipe_name+'(v_recipe_999_);'))
 for name,kind,body in mutations:
  current=dict(functions);current[name]=body
  try:inspect_functions(current)
  except ValueError:pass
  else:raise ValueError('Unsafe guard mutation accepted:'+name+':'+kind)
 review['textual_mutations_rejected']=len(mutations);review['mutation_kinds']=sorted({kind for _,kind,_ in mutations});return review

def main():
    path = Path(__file__).resolve().parent.parent / '.lake/build/ir/Tests/LocalAlignment/DocumentaryControlMeasuredAssignmentReader.c'
    review = inspect(path)
    print('DOCUMENTARY_READER_PAYMENT_CODEGEN_OK: ' +
          str(review['textual_mutations_rejected']) +
          ' textual mutants rejected; paid recipe inspection before recursive descent, ' +
          'paid received queries before prior application, whole closure captures; ' +
          'consumer inventory and mathematical laws checked separately')

if __name__ == '__main__':
    import sys
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print('DOCUMENTARY_READER_PAYMENT_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
