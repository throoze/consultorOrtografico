/**
 * Excepcion, el archivo a leer no existe...
 * @author victor
 */
class ExcepcionArchivoNoExiste extends Exception {
    
    String mensaje;
    
    public ExcepcionArchivoNoExiste(){
        super();
        mensaje = "El archivo a leer no existe...";
    }

    public ExcepcionArchivoNoExiste(String m){
        super(m);
        mensaje = m;
    }
    
    public String gerMessage ()
    {
        return mensaje;
    }
}
