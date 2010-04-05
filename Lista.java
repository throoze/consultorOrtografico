
import java.util.Iterator;

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author victor
 */
public interface Lista {

    public void agregarh (Object e);
    
    public void agregart (Object e);
    
    public void agregar (int p, Object e);
    
    public void eliminar (int p, Object e);
    
    public Object get (int p);
    
    public boolean isEmpty();
    
    public Iterator iterar ();
    
}
