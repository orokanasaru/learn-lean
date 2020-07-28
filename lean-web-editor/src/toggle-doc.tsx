import React from 'react';

interface ToggleDocProps {
  doc: string;
}

interface ToggleDocState {
  showDoc: boolean;
}

export class ToggleDoc extends React.Component<ToggleDocProps, ToggleDocState> {
  constructor(props: ToggleDocProps) {
    super(props);
    this.state = { showDoc: this.props.doc.length < 80 };
    this.onClick = this.onClick.bind(this);
  }
  onClick() {
    this.setState({ showDoc: !this.state.showDoc });
  }
  render() {
    return (
      <div onClick={this.onClick} className='toggleDoc'>
        {this.state.showDoc ? (
          this.props.doc // TODO: markdown / highlighting?
        ) : (
          <span>
            {this.props.doc.slice(0, 75)}{' '}
            <span style={{ color: '#246' }}>[...]</span>
          </span>
        )}
        <br />
        <br />
      </div>
    );
  }
}
